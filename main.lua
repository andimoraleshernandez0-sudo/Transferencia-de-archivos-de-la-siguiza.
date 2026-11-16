-- Red Social Jieshuo (estilo WhatsApp) - versión 4
-- Chats privados, grupos, grupos públicos visibles sin buscar, mensajes de voz,
-- modo llamada dentro de la app, respuestas, reenvío, menciones, favoritos,
-- frases rápidas, avisos del administrador y notificaciones en segundo plano.
-- Nuevo en la 4: buscar personas, perfiles, bloqueos, reportes, escribir al administrador,
-- códigos de invitación, mensajes destacados y responder en privado.
require "import"
import "android.app.*"
import "android.os.*"
import "android.view.*"
import "android.widget.*"
import "android.content.*"
import "android.media.MediaRecorder"
import "android.media.MediaPlayer"
import "android.media.PlaybackParams"
import "android.util.Base64"
import "android.net.Uri"
import "java.net.URL"
import "java.io.*"
import "java.util.ArrayList"
import "java.lang.System"
import "java.lang.Thread"
import "java.lang.Runnable"
import "org.json.JSONObject"

local SERVERS = {
  "https://red-social-jieshuo-accesible.vercel.app",
  "https://red-social-jieshuo-r01-accesible.vercel.app",
  "https://red-social-jieshuo-r02-accesible.vercel.app",
  "https://red-social-jieshuo-r03-accesible.vercel.app",
  "https://red-social-jieshuo-r04-accesible.vercel.app",
  "https://red-social-jieshuo-r05-accesible.vercel.app",
  "https://red-social-jieshuo-r06-accesible.vercel.app",
  "https://red-social-jieshuo-r07-accesible.vercel.app",
  "https://red-social-jieshuo-r08-accesible.vercel.app",
  "https://red-social-jieshuo-r09-accesible.vercel.app",
  "https://red-social-jieshuo-r10-accesible.vercel.app",
  "https://red-social-jieshuo-r11-accesible.vercel.app"
}
local OVERLAY = 2032 -- TYPE_ACCESSIBILITY_OVERLAY
local MAX_REC_SECONDS = 120   -- mensaje de voz normal
local MAX_CALL_SECONDS = 30   -- cada turno en el modo llamada
local MAX_MSG = 500           -- límite del servidor
local CALL_MARK = "Iniciar llamada de voz para unirte"
local ctx = service
local handler = Handler(Looper.getMainLooper())
local prefs = ctx.getSharedPreferences("red_social", 0)
local cacheDir = ctx.getCacheDir().getAbsolutePath()

local srv = prefs.getInt("lastSrv", 1) -- último servidor que funcionó (abre más rápido)
if srv < 1 or srv > #SERVERS then srv = 1 end

local state = {
  token = prefs.getString("token", ""),
  name = prefs.getString("name", ""),
  lastN = prefs.getString("lastN", ""),
  running = false,   -- la interfaz está abierta
  alive = false,     -- sesión activa (sigue en segundo plano aunque cierres la interfaz)
  polling = false, listShown = false, looping = false,
  chat = nil, dlg = nil, chats = {}, newNotices = 0, cycles = 0,
  inst = tostring(os.time()) .. tostring(math.random(1000, 9999))
}
prefs.edit().putString("inst", state.inst).commit()

local openList, openChat, startLogin, openNotices, openAppSettings, bannedScreen

------------------------------------------------------------ utilidades
local function toast(t) Toast.makeText(ctx, tostring(t), Toast.LENGTH_LONG).show() end

local function errText(o)
  local e = o.optJSONObject("error")
  if e then return "Error del servidor: " .. e.toString() end
  return o.optString("error", "Error desconocido")
end

local function showDialog(dlg)
  pcall(function()
    local win = dlg.getWindow()
    if win then
      win.setType(OVERLAY)
      win.addFlags(WindowManager.LayoutParams.FLAG_DIM_BEHIND)
      win.setDimAmount(0.6)
      local params = win.getAttributes()
      params.width = WindowManager.LayoutParams.MATCH_PARENT
      params.height = WindowManager.LayoutParams.MATCH_PARENT
      params.gravity = Gravity.FILL
      win.setAttributes(params)
      win.setLayout(WindowManager.LayoutParams.MATCH_PARENT, WindowManager.LayoutParams.MATCH_PARENT)
    end
  end)
  dlg.show()
  pcall(function()
    local win = dlg.getWindow()
    if win then
      win.addFlags(WindowManager.LayoutParams.FLAG_DIM_BEHIND)
      local params = win.getAttributes()
      params.width = WindowManager.LayoutParams.MATCH_PARENT
      params.height = WindowManager.LayoutParams.MATCH_PARENT
      params.gravity = Gravity.FILL
      win.setAttributes(params)
      win.setLayout(WindowManager.LayoutParams.MATCH_PARENT, WindowManager.LayoutParams.MATCH_PARENT)
    end
  end)
  return dlg
end

local function jarr(a)
  local t = {}
  if a then for i = 0, a.length() - 1 do t[#t + 1] = a.getString(i) end end
  return t
end

local function contains(t, v)
  for _, x in ipairs(t) do if tostring(x):lower() == tostring(v):lower() then return true end end
  return false
end

-- Corta un texto sin romper letras con acento
local function cut(s, n)
  s = tostring(s or "")
  if #s <= n then return s end
  local e = n
  while e > 0 do
    local b = s:byte(e + 1)
    if b and b >= 128 and b < 192 then e = e - 1 else break end
  end
  return s:sub(1, e)
end

local function short(s, n)
  s = tostring(s or "")
  if #s > n then return cut(s, n) .. "..." end
  return s
end

local function ulen(s)
  local _, n = tostring(s or ""):gsub("[^\128-\191]", "")
  return n
end

local function oneLine(s)
  return (tostring(s or ""):gsub("%s+", " "))
end

local function mapGet(key)
  local m = {}
  for part in string.gmatch(prefs.getString(key, ""), "[^;]+") do
    local r, id = part:match("^([^:]+):(.*)$")
    if r then m[r] = id end
  end
  return m
end

local function mapSet(key, room, id)
  if not id or id == "" then return end
  local m = mapGet(key)
  m[room] = id
  local t = {}
  for k, v in pairs(m) do t[#t + 1] = k .. ":" .. v end
  prefs.edit().putString(key, table.concat(t, ";")).commit()
end

local function setSeen(room, id) mapSet("seen", room, id) end

local function pb(key, def) return prefs.getBoolean(key, def) end
local function toggle(key, def) prefs.edit().putBoolean(key, not pb(key, def)).commit() end
local function yn(v) return v and "sí" or "no" end
local function toggleLabel(text, key, def) return text .. ": " .. yn(pb(key, def)) end

-- Listas guardadas en el teléfono (fijados, silenciados, ignorados, frases)
local function listGet(key, sep)
  local t = {}
  for part in string.gmatch(prefs.getString(key, ""), "[^" .. sep .. "]+") do t[#t + 1] = part end
  return t
end

local function listSet(key, t, sep) prefs.edit().putString(key, table.concat(t, sep)).commit() end

local function listHas(key, v, sep)
  for _, x in ipairs(listGet(key, sep)) do if x == v then return true end end
  return false
end

-- Agrega o quita; devuelve true si quedó agregado
local function listToggle(key, v, sep)
  local out, found = {}, false
  for _, x in ipairs(listGet(key, sep)) do
    if x == v then found = true else out[#out + 1] = x end
  end
  if not found then out[#out + 1] = v end
  listSet(key, out, sep)
  return not found
end

local function isPinned(id) return listHas("pinned", id, ";") end
local function isMutedChat(id) return listHas("mutedchats", id, ";") end
local function isIgnored(name) return listHas("ignored", tostring(name):lower(), "|") end

local DEFAULT_PHRASES = {"Hola", "Gracias", "De acuerdo", "Ahora te respondo", "Buenos días", "Buenas noches"}

local function getPhrases()
  if not prefs.contains("phrases") then
    local t = {}
    for i, p in ipairs(DEFAULT_PHRASES) do t[i] = p end
    return t
  end
  return listGet("phrases", "\n")
end

local function setPhrases(t) listSet("phrases", t, "\n") end

-- ¿Alguien escribió mi nombre?
local function mentionsMe(text)
  local n = tostring(state.name or ""):lower()
  if n == "" then return false end
  local s = tostring(text or ""):lower()
  local from = 1
  while true do
    local i, j = s:find(n, from, true)
    if not i then return false end
    local before = (i > 1) and s:sub(i - 1, i - 1) or ""
    local after = s:sub(j + 1, j + 1)
    if not before:match("[%w_]") and not after:match("[%w_]") then return true end
    from = i + 1
  end
end

local function hhmm(ts)
  local ok, s = pcall(function() return os.date("%H:%M", math.floor((tonumber(ts) or 0) / 1000)) end)
  return ok and s or ""
end

-- Los diálogos NUNCA cierran todo al cancelar: cada "Cancelar/Volver/No" regresa a donde estabas.
local function message(title, text, back)
  local b = AlertDialog.Builder(ctx)
  b.setTitle(title)
  b.setMessage(text)
  b.setCancelable(false)
  b.setPositiveButton("Aceptar", DialogInterface.OnClickListener{onClick = function() if back then back() end end})
  showDialog(b.create())
end

local function confirm(title, text, onYes, back)
  local b = AlertDialog.Builder(ctx)
  b.setTitle(title)
  b.setMessage(text)
  b.setCancelable(false)
  b.setPositiveButton("Sí", DialogInterface.OnClickListener{onClick = function() onYes() end})
  b.setNegativeButton("No", DialogInterface.OnClickListener{onClick = function() if back then back() end end})
  showDialog(b.create())
end

-- opts: {back = función al cancelar, password = true si el último campo es contraseña}
local function ask(title, hints, onOk, opts)
  opts = opts or {}
  local lay = LinearLayout(ctx)
  lay.setOrientation(1)
  lay.setPadding(40, 20, 40, 20)
  local fields = {}
  for i, h in ipairs(hints) do
    local e = EditText(ctx)
    e.setHint(h)
    if opts.password and i >= (opts.passFrom or #hints) then e.setInputType(pb("showpw", false) and 145 or 129) end
    lay.addView(e)
    fields[i] = e
  end
  local b = AlertDialog.Builder(ctx)
  b.setTitle(title)
  b.setView(lay)
  b.setCancelable(false)
  b.setPositiveButton("Aceptar", DialogInterface.OnClickListener{onClick = function()
    local v = {}
    for i, e in ipairs(fields) do v[i] = e.getText().toString() end
    onOk(v)
  end})
  b.setNegativeButton("Cancelar", DialogInterface.OnClickListener{onClick = function() if opts.back then opts.back() end end})
  showDialog(b.create())
end

local function pick(title, labels, onPick, back, backText)
  local b = AlertDialog.Builder(ctx)
  b.setTitle(title)
  b.setItems(labels, DialogInterface.OnClickListener{onClick = function(d, i) onPick(i + 1) end})
  b.setCancelable(false)
  b.setNegativeButton(backText or "Volver", DialogInterface.OnClickListener{onClick = function() if back then back() end end})
  return showDialog(b.create())
end

local function copyText(text, what)
  pcall(function() ctx.getSystemService(Context.CLIPBOARD_SERVICE).setPrimaryClip(ClipData.newPlainText("mensaje", text)) end)
  toast(what or "Texto copiado")
end

local function shareText(text)
  local ok = pcall(function()
    local i = Intent(Intent.ACTION_SEND)
    i.setType("text/plain")
    i.putExtra(Intent.EXTRA_TEXT, text)
    local c = Intent.createChooser(i, "Compartir mensaje")
    c.addFlags(268435456)
    ctx.startActivity(c)
  end)
  if not ok then toast("No se pudo abrir el menú de compartir.") end
end

local function fmtDate(ts)
  local ok, s = pcall(function() return os.date("%d/%m/%Y", math.floor((tonumber(ts) or 0) / 1000)) end)
  return ok and s or ""
end

local function fmtDateTime(ts)
  local ok, s = pcall(function() return os.date("%d/%m/%Y a las %H:%M", math.floor((tonumber(ts) or 0) / 1000)) end)
  return ok and s or ""
end

-- org.json devuelve "null" como texto cuando el valor es null
local function nz(s)
  s = tostring(s or "")
  if s == "null" then return "" end
  return s
end

-- Deletrea un código para que el lector lo diga letra por letra
local function spell(s) return (tostring(s):gsub(".", "%0 ")) end

-- Mensajes destacados (se guardan en el teléfono)
local MAX_STARS = 50
local function clean1(s) return (tostring(s or ""):gsub("[\t\r\n]", " ")) end

local function getStars()
  local t = {}
  for record in string.gmatch(prefs.getString("stars", ""), "[^\n]+") do
    local room, name, text = record:match("^([^\t]*)\t([^\t]*)\t(.*)$")
    if room then t[#t + 1] = {room = room, name = name, text = text} end
  end
  return t
end

local function setStars(t)
  local lines = {}
  for _, s in ipairs(t) do lines[#lines + 1] = s.room .. "\t" .. s.name .. "\t" .. s.text end
  prefs.edit().putString("stars", table.concat(lines, "\n")).commit()
end

------------------------------------------------------------ notificaciones de Android
local nm = ctx.getSystemService(Context.NOTIFICATION_SERVICE)
local CH = "red_social_msgs"
pcall(function()
  if Build.VERSION.SDK_INT >= 26 then nm.createNotificationChannel(NotificationChannel(CH, "Red Social", 4)) end
end)

local function nid(s)
  local n = 0
  for i = 1, #s do n = (n * 31 + s:byte(i)) % 100000 end
  return 1000 + n
end

local function notify(id, title, text)
  return pcall(function()
    local nb
    if Build.VERSION.SDK_INT >= 26 then nb = Notification.Builder(ctx, CH) else nb = Notification.Builder(ctx) end
    nb.setSmallIcon(android.R.drawable.ic_dialog_email)
    nb.setContentTitle(title)
    nb.setContentText(text)
    nb.setAutoCancel(true)
    nm.notify(id, nb.build())
  end)
end

local function uiVisible() return state.chat ~= nil or state.listShown end

-- Aviso del administrador: primero se anuncia "Aviso del administrador" y enseguida
-- aparece un diálogo con el texto del aviso.
local noticeQueue, noticeShowing = {}, false
local function showNextNotice()
  if noticeShowing or #noticeQueue == 0 then return end
  noticeShowing = true
  local n = table.remove(noticeQueue, 1)
  toast("Aviso del administrador")
  handler.postDelayed(Runnable{run = function()
    local b = AlertDialog.Builder(ctx)
    b.setTitle("Aviso del administrador")
    b.setMessage(n.title .. ". " .. n.text)
    b.setCancelable(false)
    b.setPositiveButton("Entendido", DialogInterface.OnClickListener{onClick = function() end})
    local dlg = b.create()
    dlg.setOnDismissListener(DialogInterface.OnDismissListener{onDismiss = function()
      noticeShowing = false
      showNextNotice()
    end})
    showDialog(dlg)
  end}, 1500)
end

local function queueNotice(title, text)
  noticeQueue[#noticeQueue + 1] = {title = title, text = text}
  if not uiVisible() then notify(nid("aviso" .. title), "Aviso del administrador", title .. ". " .. text) end
  showNextNotice()
end

------------------------------------------------------------ red
local function isBan(obj) return errText(obj):find("baneado") ~= nil end

local function logout(msg)
  state.running = false
  state.alive = false
  state.token = ""
  prefs.edit().remove("token").commit()
  if state.dlg then pcall(function() state.dlg.dismiss() end) end
  if msg then toast(msg) end
  startLogin(false)
end

function bannedScreen(msg)
  state.running = false
  state.alive = false
  if state.dlg then pcall(function() state.dlg.dismiss() end) end
  local b = AlertDialog.Builder(ctx)
  b.setTitle("Has sido baneado")
  b.setMessage(msg)
  b.setCancelable(false)
  b.setPositiveButton("Cerrar", nil)
  showDialog(b.create())
end

local closedShown = false
local function closedScreen(msg)
  state.alive = false
  state.running = false
  if closedShown then return end
  closedShown = true
  if state.dlg then pcall(function() state.dlg.dismiss() end) end
  local b = AlertDialog.Builder(ctx)
  b.setTitle("Servidor cerrado")
  b.setMessage(tostring(msg) .. "\n\nVuelve a abrir el complemento más tarde.")
  b.setCancelable(false)
  b.setPositiveButton("Cerrar", DialogInterface.OnClickListener{onClick = function() closedShown = false end})
  showDialog(b.create())
end

-- cb(código, JSONObject, error)
local function request(method, path, data, cb)
  Thread(Runnable{run = function()
    local code, text = 0, ""
    local ok = false
    for attempt = 0, #SERVERS - 1 do
      local idx = ((srv - 1 + attempt) % #SERVERS) + 1
      code, text = 0, ""
      ok = pcall(function()
        local c = URL(SERVERS[idx] .. path).openConnection()
        c.setRequestMethod(method)
        c.setConnectTimeout(4000)
        c.setReadTimeout(12000)
        c.setRequestProperty("Content-Type", "application/json")
        if state.token ~= "" then c.setRequestProperty("Authorization", "Bearer " .. state.token) end
        if data then
          local o = JSONObject()
          for k, v in pairs(data) do o.put(k, tostring(v)) end
          c.setDoOutput(true)
          local w = OutputStreamWriter(c.getOutputStream(), "UTF-8")
          w.write(o.toString())
          w.flush()
          w.close()
        end
        code = c.getResponseCode()
        local stream = (code >= 400) and c.getErrorStream() or c.getInputStream()
        local br = BufferedReader(InputStreamReader(stream, "UTF-8"))
        local parts = {}
        local line = br.readLine()
        while line do parts[#parts + 1] = line; line = br.readLine() end
        br.close()
        text = table.concat(parts, "\n")
      end)
      if ok and code < 500 then
        srv = idx
        prefs.edit().putInt("lastSrv", srv).commit()
        break
      end
    end
    handler.post(Runnable{run = function()
      if not ok then cb(0, nil, "No se pudo conectar con el servidor.") return end
      local pok, obj = pcall(function() return JSONObject(text) end)
      if not pok then cb(code, nil, "Respuesta no válida del servidor (código " .. code .. ").") return end
      if code == 423 then closedScreen(errText(obj)) return end
      if state.token ~= "" and code == 403 and isBan(obj) then bannedScreen(errText(obj)) return end
      if state.token ~= "" and code == 401 then logout(errText(obj)) return end
      cb(code, obj, nil)
    end})
  end}).start()
end

local function doPost(data, okMsg, after)
  request("POST", "/api/rooms", data, function(code, o, err)
    if err then toast(err) return end
    if not o.optBoolean("ok") then toast(errText(o)) return end
    if okMsg then toast(okMsg) end
    if after then after(o) end
  end)
end

local function serverName(i)
  if i == 1 then return "Principal" end
  return "Respaldo " .. (i - 1)
end

-- Revisa los 12 servidores y dice cuáles responden
local function testServers(back)
  toast("Probando los servidores. Puede tardar unos segundos.")
  Thread(Runnable{run = function()
    local res = {}
    for i = 1, #SERVERS do
      local t0 = System.currentTimeMillis()
      local code, closed = 0, false
      local ok = pcall(function()
        local c = URL(SERVERS[i] .. "/api/info").openConnection()
        c.setConnectTimeout(3000)
        c.setReadTimeout(5000)
        code = c.getResponseCode()
        local stream = (code >= 400) and c.getErrorStream() or c.getInputStream()
        local br = BufferedReader(InputStreamReader(stream, "UTF-8"))
        local parts = {}
        local line = br.readLine()
        while line do parts[#parts + 1] = line; line = br.readLine() end
        br.close()
        local o = JSONObject(table.concat(parts, "\n"))
        closed = o.optBoolean("closed")
      end)
      local ms = System.currentTimeMillis() - t0
      local line
      if ok and (code == 200 or code == 423) then
        line = serverName(i) .. ": " .. ((closed or code == 423) and "cerrado por el administrador" or "funciona") .. " (" .. ms .. " ms)"
      elseif code ~= 0 then
        line = serverName(i) .. ": responde con error " .. code
      else
        line = serverName(i) .. ": sin respuesta"
      end
      res[#res + 1] = line
    end
    handler.post(Runnable{run = function()
      message("Estado de los servidores", "Servidor en uso: " .. serverName(srv) .. "\n\n" .. table.concat(res, "\n"), back)
    end})
  end}).start()
end

------------------------------------------------------------ personas, perfiles, bloqueos, reportes e invitaciones
local personMenu

local function ignoreSet(name, on)
  if on ~= isIgnored(name) then listToggle("ignored", tostring(name):lower(), "|") end
end

local function startDM(name)
  doPost({action = "dm", user = name}, nil, function(o)
    state.running = true
    openChat({id = o.optString("id"), name = name, type = "dm"})
  end)
end

-- Bloquear en el servidor (no puede escribirte en privado) y también ocultar sus mensajes en este teléfono
local function blockPerson(name, on, back)
  request("POST", "/api/people", {action = on and "block" or "unblock", user = name}, function(code, o, err)
    if err then toast(err) back() return end
    if not o.optBoolean("ok") then toast(errText(o)) back() return end
    ignoreSet(name, on)
    toast(on and (name .. " fue bloqueado. No podrá escribirte y no verás sus mensajes.") or (name .. " fue desbloqueado."))
    back()
  end)
end

local function reportPerson(name, back)
  ask("Reportar a " .. name, {"Motivo (opcional)"}, function(v)
    request("POST", "/api/report", {kind = "user", user = name, reason = v[1]}, function(code, o, err)
      if err then toast(err) back() return end
      if not o.optBoolean("ok") then toast(errText(o)) back() return end
      message("Reporte enviado", "El administrador revisará tu reporte sobre " .. name .. ".", back)
    end)
  end, {back = back})
end

function personMenu(name, back)
  request("GET", "/api/people?action=profile&name=" .. Uri.encode(name), nil, function(code, o, err)
    if err then toast(err) back() return end
    if not o.optBoolean("ok") then toast(errText(o)) back() return end
    local p = o.optJSONObject("profile")
    local shown = p.optString("name")
    local bio = nz(p.optString("bio"))
    local groups = jarr(p.optJSONArray("groups"))
    local blocked, itself = p.optBoolean("blocked"), p.optBoolean("self")
    local here = function() personMenu(name, back) end
    local labels, acts = {}, {}
    local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
    add("Ver perfil", function()
      local t = {shown, (bio ~= "" and bio or "Sin descripción."), "En la red desde el " .. fmtDate(p.optLong("since")) .. "."}
      if #groups > 0 then t[#t + 1] = "Grupos en común: " .. table.concat(groups, ", ") .. "." end
      if blocked then t[#t + 1] = "La tienes bloqueada." end
      message("Perfil de " .. shown, table.concat(t, "\n"), here)
    end)
    if not itself then
      add("Escribirle un mensaje privado", function() startDM(shown) end)
      if blocked then
        add("Desbloquear", function() blockPerson(shown, false, here) end)
      else
        add("Bloquear (no podrá escribirte y no verás sus mensajes)", function()
          confirm("Bloquear a " .. shown, "No podrá escribirte en privado y no verás sus mensajes. Puedes desbloquearlo cuando quieras. ¿Bloquear?", function() blockPerson(shown, true, here) end, here)
        end)
      end
      add("Reportar a esta persona", function() reportPerson(shown, here) end)
    end
    pick(shown, labels, function(i) acts[i]() end, back)
  end)
end

-- Lista de personas (primero todas, y la primera opción sirve para buscar por nombre)
local function choosePerson(title, back, onPick, q)
  q = q or ""
  request("GET", "/api/people?action=search&q=" .. Uri.encode(q), nil, function(code, o, err)
    if err then toast(err) back() return end
    if not o.optBoolean("ok") then toast(errText(o)) back() return end
    local arr = o.optJSONArray("people")
    local labels, names = {"Buscar por nombre..."}, {false}
    for i = 0, arr.length() - 1 do
      local p = arr.getJSONObject(i)
      local bio = nz(p.optString("bio"))
      names[#names + 1] = p.optString("name")
      labels[#labels + 1] = p.optString("name") .. (bio ~= "" and (". " .. short(bio, 60)) or "")
    end
    local n = #labels - 1
    local ttl = (q ~= "") and (title .. " con \"" .. q .. "\" (" .. n .. ")") or (title .. " (" .. n .. ")")
    if n == 0 then toast("No se encontró a nadie" .. ((q ~= "") and " con ese nombre." or ".")) end
    pick(ttl, labels, function(i)
      if i == 1 then
        ask("Buscar personas", {"Parte del nombre"}, function(v) choosePerson(title, back, onPick, v[1]) end, {back = function() choosePerson(title, back, onPick, q) end})
      else
        onPick(names[i])
      end
    end, back)
  end)
end

local function openPeople()
  choosePerson("Personas", openList, function(name) personMenu(name, openPeople) end)
end

local function manageBlocked(back)
  request("GET", "/api/people?action=blocks", nil, function(code, o, err)
    if err then toast(err) back() return end
    if not o.optBoolean("ok") then toast(errText(o)) back() return end
    local names = jarr(o.optJSONArray("blocked"))
    if #names == 0 then message("Personas bloqueadas", "No tienes personas bloqueadas.", back) return end
    pick("Personas bloqueadas (" .. #names .. ")", names, function(i)
      local n = names[i]
      confirm("Desbloquear", "¿Desbloquear a " .. n .. "?", function()
        blockPerson(n, false, function() manageBlocked(back) end)
      end, function() manageBlocked(back) end)
    end, back)
  end)
end

local function editBio(back)
  request("GET", "/api/people?action=profile&name=" .. Uri.encode(state.name), nil, function(code, o, err)
    local cur = ""
    if not err and o and o.optBoolean("ok") then
      local p = o.optJSONObject("profile")
      if p then cur = nz(p.optString("bio")) end
    end
    ask("Mi descripción", {cur ~= "" and ("Ahora dice: " .. short(cur, 80)) or "Escribe algo sobre ti (máximo 140 letras)"}, function(v)
      request("POST", "/api/people", {action = "bio", text = v[1]}, function(c2, o2, e2)
        if e2 then toast(e2) back() return end
        if not o2.optBoolean("ok") then toast(errText(o2)) back() return end
        local saved = nz(o2.optString("bio"))
        message("Descripción guardada", saved ~= "" and ("Ahora dice: " .. saved) or "Tu descripción quedó vacía.", back)
      end)
    end, {back = back})
  end)
end

local function contactAdmin(back)
  ask("Escribir al administrador", {"Tu mensaje"}, function(v)
    request("POST", "/api/report", {kind = "contact", text = v[1]}, function(code, o, err)
      if err then toast(err) back() return end
      if not o.optBoolean("ok") then toast(errText(o)) back() return end
      message("Enviado", "Tu mensaje llegó al administrador.", back)
    end)
  end, {back = back})
end

-- Código de invitación de un grupo (para administradores del grupo)
local function inviteMenu(chat, back)
  request("GET", "/api/invite?room=" .. chat.id, nil, function(code, o, err)
    if err then toast(err) back() return end
    if not o.optBoolean("ok") then toast(errText(o)) back() return end
    local c = nz(o.optString("code"))
    local here = function() inviteMenu(chat, back) end
    local labels, acts = {}, {}
    local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
    local function create()
      request("POST", "/api/invite", {action = "create", room = chat.id}, function(c2, o2, e2)
        if e2 then toast(e2) back() return end
        if not o2.optBoolean("ok") then toast(errText(o2)) back() return end
        here()
      end)
    end
    local function revoke(then_)
      request("POST", "/api/invite", {action = "revoke", room = chat.id}, function(c2, o2, e2)
        if e2 then toast(e2) back() return end
        if not o2.optBoolean("ok") then toast(errText(o2)) back() return end
        then_()
      end)
    end
    if c == "" then
      add("Crear un código de invitación", create)
    else
      add("Leer el código: " .. spell(c), function()
        message("Código de invitación", "El código es: " .. spell(c) .. ". Quien lo escriba en la opción Unirme con un código entra a este grupo, aunque sea privado.", here)
      end)
      add("Copiar el código", function() copyText(c, "Código copiado") here() end)
      add("Compartir el código", function() shareText("Únete a mi grupo " .. tostring(chat.title) .. " en Red Social Jieshuo con este código: " .. c) here() end)
      add("Cambiar por un código nuevo", function() revoke(create) end)
      add("Desactivar el código", function() revoke(function() toast("Código desactivado.") here() end) end)
    end
    pick("Código de invitación", labels, function(i) acts[i]() end, back)
  end)
end

local function joinWithCode()
  ask("Unirme con un código", {"Código de invitación (8 letras y números)"}, function(v)
    request("POST", "/api/invite", {action = "join", code = v[1]}, function(code, o, err)
      if err then toast(err) openList() return end
      if not o.optBoolean("ok") then toast(errText(o)) openList() return end
      state.running = true
      openChat({id = o.optString("id"), name = o.optString("name"), type = "group"})
    end)
  end, {back = openList})
end

local function manageStars(back)
  local list = getStars()
  if #list == 0 then message("Mensajes destacados", "No has destacado mensajes. Toca un mensaje de texto y elige Destacar.", back) return end
  local labels = {}
  for i, s in ipairs(list) do labels[i] = s.name .. ": " .. short(s.text, 80) end
  pick("Mensajes destacados (" .. #list .. ")", labels, function(i)
    local s = list[i]
    local here = function() manageStars(back) end
    pick(s.name, {"Leer completo", "Copiar", "Compartir con otras aplicaciones", "Quitar de destacados"}, function(j)
      if j == 1 then message(s.name, s.text, here)
      elseif j == 2 then copyText(s.text) here()
      elseif j == 3 then shareText(s.name .. ": " .. s.text) here()
      else table.remove(list, i) setStars(list) toast("Quitado de destacados.") here() end
    end, here)
  end, back)
end

local function showNews(back)
  message("Novedades de la versión 4", table.concat({
    "Personas: busca a cualquiera por una parte del nombre, mira su perfil y escríbele en privado.",
    "Bloquear: quien bloqueas no puede escribirte en privado y no ves sus mensajes.",
    "Reportar: toca un mensaje y elige Reportar. También puedes escribir al administrador desde Ajustes.",
    "Códigos de invitación: los administradores de un grupo crean un código y quien lo escribe entra, aunque sea privado.",
    "Mensajes destacados: guarda mensajes importantes y léelos desde Ajustes.",
    "Responder en privado: toca un mensaje y elige Escribirle en privado.",
    "Tu descripción: cuenta algo sobre ti desde Ajustes."
  }, "\n"), back)
end

------------------------------------------------------------ audio
local player = nil
local audioBusy = false
local audioQueue = {}

local function stopAudio()
  if player then
    pcall(function() player.stop() end)
    pcall(function() player.release() end)
    player = nil
  end
  audioBusy = false
end

local function stopAllAudio()
  audioQueue = {}
  stopAudio()
end

local function playbackSpeed()
  local s = tonumber(prefs.getString("speed", "1.0")) or 1.0
  if s < 0.5 or s > 3 then s = 1.0 end
  return s
end

-- onFinish (opcional): se llama cuando termina de sonar o si falla
local function playAudio(room, id, onFinish)
  local path = cacheDir .. "/a_" .. id .. ".m4a"
  local function finish()
    stopAudio()
    if onFinish then onFinish() end
  end
  local function play()
    stopAudio()
    audioBusy = true
    local ok = pcall(function()
      player = MediaPlayer()
      player.setDataSource(path)
      player.prepare()
      player.setOnCompletionListener(MediaPlayer.OnCompletionListener{onCompletion = function() finish() end})
      local sp = playbackSpeed()
      if sp ~= 1.0 then
        pcall(function() player.setPlaybackParams(PlaybackParams().setSpeed(sp)) end)
      end
      player.start()
    end)
    if not ok then
      toast("No se pudo reproducir el audio.")
      finish()
    end
  end
  if File(path).exists() then play() return end
  if not onFinish then toast("Descargando audio") end
  Thread(Runnable{run = function()
    local ok = false
    for attempt = 0, 2 do
      local idx = ((srv - 1 + attempt) % #SERVERS) + 1
      ok = pcall(function()
        local c = URL(SERVERS[idx] .. "/api/audio?room=" .. room .. "&id=" .. id).openConnection()
        c.setRequestProperty("Authorization", "Bearer " .. state.token)
        c.setConnectTimeout(4000)
        c.setReadTimeout(15000)
        if c.getResponseCode() ~= 200 then error("http") end
        local ins = c.getInputStream()
        local out = FileOutputStream(path)
        local buf = byte[4096]
        local n = ins.read(buf)
        while n ~= -1 do out.write(buf, 0, n); n = ins.read(buf) end
        out.close()
        ins.close()
      end)
      if ok then break end
    end
    handler.post(Runnable{run = function()
      if ok then play() else
        pcall(function() File(path).delete() end)
        toast("No se pudo descargar el audio.")
        audioBusy = false
        if onFinish then onFinish() end
      end
    end})
  end}).start()
end

-- Cola de reproducción automática (llamada o reproducción automática): los audios suenan uno tras otro
local function nextInQueue()
  if audioBusy or #audioQueue == 0 then return end
  local a = table.remove(audioQueue, 1)
  audioBusy = true
  playAudio(a.room, a.id, nextInQueue)
end

local function enqueueAudio(room, id)
  audioQueue[#audioQueue + 1] = {room = room, id = id}
  nextInQueue()
end

local rec, recPath, recStart, recId = nil, "", 0, 0

local function startRec()
  recPath = cacheDir .. "/rec_" .. os.time() .. ".m4a"
  local ok = pcall(function()
    rec = MediaRecorder()
    rec.setAudioSource(1)
    rec.setOutputFormat(2)
    rec.setAudioEncoder(3)
    rec.setAudioChannels(1)
    rec.setAudioSamplingRate(44100)  -- calidad alta
    rec.setAudioEncodingBitRate(96000)
    rec.setOutputFile(recPath)
    rec.prepare()
    rec.start()
  end)
  if not ok then
    pcall(function() rec.release() end)
    rec = nil
    toast("No se pudo grabar. Revisa que Jieshuo tenga permiso de micrófono.")
    return false
  end
  recStart = System.currentTimeMillis()
  recId = recId + 1
  return true
end

local function stopRec(discard)
  if not rec then return nil, 0 end
  local secs = math.max(1, math.floor((System.currentTimeMillis() - recStart) / 1000 + 0.5))
  pcall(function() rec.stop() end)
  pcall(function() rec.release() end)
  rec = nil
  recId = recId + 1
  if discard then pcall(function() File(recPath).delete() end) return nil, 0 end
  return recPath, secs
end

local function sendAudioFile(room, path, secs, cb)
  Thread(Runnable{run = function()
    local ok, b64 = pcall(function()
      local fis = FileInputStream(path)
      local bos = ByteArrayOutputStream()
      local buf = byte[4096]
      local n = fis.read(buf)
      while n ~= -1 do bos.write(buf, 0, n); n = fis.read(buf) end
      fis.close()
      return Base64.encodeToString(bos.toByteArray(), 2)
    end)
    handler.post(Runnable{run = function()
      pcall(function() File(path).delete() end)
      if not ok then cb(0, nil, "No se pudo leer la grabación.") return end
      request("POST", "/api/send", {room = room, audio = b64, secs = secs}, cb)
    end})
  end}).start()
end

local function cleanAudios(back)
  confirm("Eliminar audios", "Se borrarán los mensajes de voz descargados y las grabaciones temporales de este dispositivo para liberar espacio. ¿Continuar?", function()
    Thread(Runnable{run = function()
      local deleted, failed = 0, 0
      local files = File(cacheDir).listFiles()
      if files then
        local i = 0
        while true do
          local ok, f = pcall(function() return files[i] end)
          if not ok or not f then break end
          local name = f.getName()
          if name and (name:match("^a_") or name:match("^rec_")) and name:match("%.m4a$") then
            if f.delete() then deleted = deleted + 1 else failed = failed + 1 end
          end
          i = i + 1
        end
      end
      handler.post(Runnable{run = function()
        toast("Audios eliminados: " .. deleted .. (failed > 0 and (" (fallaron " .. failed .. ")") or "") .. ".")
        if back then back() end
      end})
    end}).start()
  end, back)
end

------------------------------------------------------------ ajustes del chat (grupo)
local function openSettings(chat)
  request("GET", "/api/rooms?action=info&room=" .. chat.id, nil, function(code, o, err)
    if err then toast(err) return end
    if not o.optBoolean("ok") then toast(errText(o)) return end
    local r = o.optJSONObject("room")
    local role = o.optString("role")
    local info = {
      name = r.optString("name"), desc = r.optString("desc"), type = r.optString("type"),
      privacy = r.optString("privacy"), owner = r.optString("owner"),
      admins = jarr(r.optJSONArray("admins")), members = jarr(r.optJSONArray("members")),
      onlyAdmins = r.optBoolean("onlyAdmins")
    }
    local isAdm = (role == "owner" or role == "admin")
    local labels, acts = {}, {}
    local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
    local again = function() openSettings(chat) end

    local function membersMenu()
      local ml, names = {}, {}
      for _, n in ipairs(info.members) do
        local tag = ""
        if n:lower() == info.owner:lower() then tag = " (propietario)"
        elseif contains(info.admins, n) then tag = " (administrador)" end
        ml[#ml + 1] = n .. tag
        names[#names + 1] = n
      end
      pick("Miembros (" .. #names .. ")", ml, function(i)
        local n = names[i]
        if not isAdm or n:lower() == state.name:lower() or n:lower() == info.owner:lower() then again() return end
        local ol, of = {}, {}
        local isA = contains(info.admins, n)
        if role == "owner" then
          ol[#ol + 1] = isA and "Quitar de administradores" or "Hacer administrador"
          of[#of + 1] = function() doPost({action = "admin", room = chat.id, user = n, value = tostring(not isA)}, "Listo.") end
        end
        if not isA or role == "owner" then
          ol[#ol + 1] = "Quitar del grupo"
          of[#of + 1] = function() confirm("Quitar a " .. n, "¿Quitar a " .. n .. " del grupo?", function() doPost({action = "remove", room = chat.id, user = n}, n .. " fue quitado del grupo.") end) end
        end
        if #ol == 0 then again() return end
        pick(n, ol, function(j) of[j]() end, again)
      end, again)
    end

    if info.type == "dm" then
      add("Información del chat", function() message("Chat privado", "Conversación privada entre " .. table.concat(info.members, " y ") .. ".", again) end)
      add("Eliminar este chat de mi lista", function()
        confirm("Eliminar chat", "Se quitará de tu lista. Podrás volver a abrirlo cuando quieras.", function()
          doPost({action = "leave", room = chat.id}, "Chat eliminado de tu lista.", function() chat.close() end)
        end, again)
      end)
    elseif o.optBoolean("general") then
      add("Información", function() message("General", "Sala pública donde están todos los usuarios. No se puede abandonar.", again) end)
    else
      add("Información del grupo", function()
        message(info.name, (info.desc ~= "" and (info.desc .. "\n\n") or "") .. "Grupo " .. (info.privacy == "public" and "público" or "privado") .. ". Propietario: " .. info.owner .. ". " .. #info.members .. " miembros." .. (info.onlyAdmins and " Solo los administradores pueden escribir." or ""), again)
      end)
      add("Ver miembros (" .. #info.members .. ")", membersMenu)
      if isAdm then
        add("Agregar miembro (buscar a la persona)", function()
          choosePerson("Agregar a", again, function(name) doPost({action = "add", room = chat.id, user = name}, "Persona agregada.", again) end)
        end)
        add("Código de invitación del grupo", function() inviteMenu(chat, again) end)
        add("Cambiar nombre del grupo", function()
          ask("Nombre del grupo", {"Nuevo nombre"}, function(v) doPost({action = "update", room = chat.id, name = v[1]}, "Nombre cambiado.") end, {back = again})
        end)
        add("Cambiar descripción", function()
          ask("Descripción", {"Nueva descripción"}, function(v) doPost({action = "update", room = chat.id, desc = v[1]}, "Descripción cambiada.") end, {back = again})
        end)
        add(info.privacy == "public" and "Hacer el grupo privado (solo por invitación)" or "Hacer el grupo público (cualquiera puede unirse)", function()
          doPost({action = "update", room = chat.id, privacy = (info.privacy == "public") and "private" or "public"}, "Privacidad cambiada.")
        end)
        add(info.onlyAdmins and "Permitir que todos escriban" or "Solo los administradores pueden escribir", function()
          doPost({action = "update", room = chat.id, onlyAdmins = tostring(not info.onlyAdmins)}, "Ajuste cambiado.")
        end)
      end
      add("Salir del grupo", function()
        confirm("Salir del grupo", "¿Quieres salir de " .. info.name .. "?", function()
          doPost({action = "leave", room = chat.id}, "Saliste del grupo.", function() chat.close() end)
        end, again)
      end)
      if role == "owner" then
        add("Eliminar el grupo para todos", function()
          confirm("Eliminar grupo", "Se borrará el grupo y todos sus mensajes para todos. No se puede deshacer. ¿Seguro?", function()
            doPost({action = "delete", room = chat.id}, "Grupo eliminado.", function() chat.close() end)
          end, again)
        end)
      end
    end
    pick("Ajustes de " .. chat.title, labels, function(i) acts[i]() end)
  end)
end

------------------------------------------------------------ sondeo, segundo plano y avisos
local function lineFor(m)
  local kind = m.optString("kind", "text")
  local t = pb("showtime", false) and (" (" .. hhmm(m.optLong("ts")) .. ")") or ""
  if kind == "system" then return "— " .. m.optString("text") end
  if kind == "audio" then return m.optString("name") .. ": mensaje de voz de " .. m.optInt("secs") .. " segundos" .. t .. ". Toca para escuchar." end
  return m.optString("name") .. ": " .. m.optString("text") .. t
end

local function handleNotices(o, chat)
  local ns = o.optJSONArray("notifications")
  if ns then
    for i = 0, ns.length() - 1 do
      local n = ns.getJSONObject(i)
      state.newNotices = state.newNotices + 1
      if chat then chat.add("Aviso del administrador - " .. n.optString("title") .. ": " .. n.optString("text"), {kind = "notif"}) end
      queueNotice(n.optString("title"), n.optString("text"))
    end
  end
  state.lastN = o.optString("lastNotificationId", state.lastN)
  prefs.edit().putString("lastN", state.lastN).commit()
end

local function doPoll(done)
  if state.polling or not state.alive then if done then done() end return end
  local chat = state.chat
  if not chat then if done then done() end return end
  state.polling = true
  local path = "/api/poll?nafter=" .. Uri.encode(state.lastN) .. "&room=" .. chat.id .. "&after=" .. Uri.encode(chat.lastId)
  request("GET", path, nil, function(code, o, err)
    state.polling = false
    if o and (code == 403 or code == 404) and chat and state.chat == chat then
      toast(errText(o))
      chat.close()
    elseif o and o.optBoolean("ok") then
      local heard = {}
      if state.chat == chat and o.optString("room") == chat.id then
        local first = (chat.lastId == "")
        local msgs = o.optJSONArray("messages")
        if msgs then
          for i = 0, msgs.length() - 1 do
            local m = msgs.getJSONObject(i)
            local kind = m.optString("kind", "text")
            local text = m.optString("text")
            local who = m.optString("name")
            local mine = (who == state.name)
            if kind ~= "system" and not mine and isIgnored(who) then
              -- usuario ignorado: no se muestra
            else
              chat.add(lineFor(m), {kind = kind, id = m.optString("id"), name = who, text = text, ts = m.optLong("ts")})
              if not first and not mine and kind ~= "system" then
                if kind == "audio" then
                  if chat.callMode or pb("autoplay", false) then
                    enqueueAudio(chat.id, m.optString("id"))
                  elseif not isMutedChat(chat.id) then
                    heard[#heard + 1] = who .. " envió un mensaje de voz"
                  end
                elseif pb("mentions", true) and mentionsMe(text) then
                  heard[#heard + 1] = who .. " te mencionó: " .. text
                elseif not isMutedChat(chat.id) then
                  heard[#heard + 1] = who .. ": " .. text
                end
              end
            end
          end
        end
        chat.lastId = o.optString("lastMessageId", chat.lastId)
        setSeen(chat.id, chat.lastId)
      end
      handleNotices(o, state.chat)
      if #heard > 0 and pb("speak", true) then toast(table.concat(heard, ". ")) end
    end
    if done then done() end
  end)
end

local function deliver(items)
  if #items == 0 then return end
  local lines = {}
  for _, it in ipairs(items) do
    local c = it.c
    local who = c.optString("lastName")
    local what = (c.optString("kind") == "audio") and "mensaje de voz" or c.optString("lastText")
    local isGroup = (c.optString("type") == "group" and c.optString("rname") ~= "")
    local title = (c.optString("type") == "dm" or c.optString("rname") == "") and who or c.optString("rname")
    local text = (isGroup and (who .. ": ") or "") .. what
    if it.mention then
      title = isGroup and (who .. " te mencionó en " .. c.optString("rname")) or (who .. " te mencionó")
      text = what
    end
    if uiVisible() then
      lines[#lines + 1] = title .. ". " .. text
    else
      if not notify(nid(c.optString("id")), title, text) then lines[#lines + 1] = title .. ". " .. text end
    end
  end
  if #lines > 0 and pb("speak", true) then toast("Mensaje nuevo. " .. table.concat(lines, ". ")) end
end

local function doInbox(done)
  if state.polling or not state.alive then if done then done() end return end
  state.polling = true
  request("GET", "/api/inbox?nafter=" .. Uri.encode(state.lastN), nil, function(code, o, err)
    state.polling = false
    if o and o.optBoolean("ok") then
      handleNotices(o, nil)
      local arr = o.optJSONArray("chats")
      local seen, notified = mapGet("seen"), mapGet("notified")
      local items = {}
      if arr then
        for i = 0, arr.length() - 1 do
          local c = arr.getJSONObject(i)
          local id, lastId = c.optString("id"), c.optString("lastId")
          if notified[id] == nil then
            mapSet("notified", id, seen[id] or lastId) -- primera sincronización: sin avisar
          else
            if lastId > notified[id] then
              local lastName = c.optString("lastName")
              if lastId > (seen[id] or "") and lastName ~= state.name and c.optString("kind") ~= "system" and not isIgnored(lastName) then
                local mention = (c.optString("kind") ~= "audio") and pb("mentions", true) and mentionsMe(c.optString("lastText"))
                local allowed = (id ~= "general" or pb("notifyGeneral", false)) and not isMutedChat(id)
                if mention or allowed then items[#items + 1] = {c = c, mention = mention} end
              end
              mapSet("notified", id, lastId)
            end
          end
        end
      end
      deliver(items)
    end
    if done then done() end
  end)
end

local function cycle()
  if not state.alive or prefs.getString("inst", "") ~= state.inst then state.looping = false return end
  local delay = 25000
  if state.chat then delay = state.chat.callMode and 2000 or 4000
  elseif state.listShown then delay = 12000 end
  local function again() handler.postDelayed(Runnable{run = cycle}, delay) end
  if not uiVisible() and not pb("bg", true) then again() return end
  if state.chat then
    doPoll(function()
      state.cycles = state.cycles + 1
      if state.cycles % 4 == 0 and pb("bg", true) then doInbox(again) else again() end
    end)
  else
    doInbox(again)
  end
end

local function startLoop()
  if state.looping then return end
  state.looping = true
  cycle()
end

------------------------------------------------------------ chat
function openChat(c)
  local title = c.title
  if not title then
    if c.type == "dm" then
      title = c.name or ""
      if title == "" and c.members then
        for _, m in ipairs(c.members) do if m:lower() ~= state.name:lower() then title = m end end
      end
    else
      title = c.name or "Chat"
    end
  end
  local chat = {id = c.id, title = title, type = c.type or "group", lastId = "", entries = {}, lines = {}, callMode = false, replyTo = nil, role = "member", noList = false}
  state.chat = chat

  local lay = LinearLayout(ctx)
  lay.setOrientation(1)
  lay.setPadding(12, 8, 12, 8)
  lay.setBackgroundColor(0xFFFFFFFF)
  local header = TextView(ctx)
  header.setText(title)
  lay.addView(header)
  local data = ArrayList()
  local adapter = ArrayAdapter(ctx, android.R.layout.simple_list_item_1, data)
  local lv = ListView(ctx)
  lv.setAdapter(adapter)
  lv.setTranscriptMode(2)
  lay.addView(lv, LinearLayout.LayoutParams(-1, 0, 1))
  local input = EditText(ctx)
  input.setHint("Escribe tu mensaje")
  local draft = prefs.getString("draft_" .. c.id, "")
  if draft ~= "" then input.setText(draft) end
  lay.addView(input)

  local row1 = LinearLayout(ctx); row1.setOrientation(0)
  local row2 = LinearLayout(ctx); row2.setOrientation(0)
  local row3 = LinearLayout(ctx); row3.setOrientation(0)
  local row4 = LinearLayout(ctx); row4.setOrientation(0)
  local send = Button(ctx); send.setText("Enviar")
  local recBtn = Button(ctx); recBtn.setText("Grabar mensaje de voz")
  local callBtn = Button(ctx); callBtn.setText("Iniciar llamada de voz")
  local phrasesBtn = Button(ctx); phrasesBtn.setText("Frases rápidas")
  local moreBtn = Button(ctx); moreBtn.setText("Más opciones")
  local settings = Button(ctx); settings.setText("Ajustes del chat")
  local cancel = Button(ctx); cancel.setText("Descartar grabación"); cancel.setVisibility(8)
  local back = Button(ctx); back.setText("Volver")
  row1.addView(send, LinearLayout.LayoutParams(0, -2, 1))
  row1.addView(recBtn, LinearLayout.LayoutParams(0, -2, 1))
  row2.addView(callBtn, LinearLayout.LayoutParams(0, -2, 1))
  row2.addView(phrasesBtn, LinearLayout.LayoutParams(0, -2, 1))
  row3.addView(moreBtn, LinearLayout.LayoutParams(0, -2, 1))
  row3.addView(settings, LinearLayout.LayoutParams(0, -2, 1))
  row4.addView(cancel, LinearLayout.LayoutParams(0, -2, 1))
  row4.addView(back, LinearLayout.LayoutParams(0, -2, 1))
  lay.addView(row1)
  lay.addView(row2)
  lay.addView(row3)
  lay.addView(row4)

  local b = AlertDialog.Builder(ctx)
  b.setView(lay)
  local dlg = b.create()
  state.dlg = dlg

  local function rebuild()
    adapter.clear()
    for _, l in ipairs(chat.lines) do adapter.add(l) end
  end

  function chat.add(line, entry)
    chat.entries[#chat.entries + 1] = entry
    chat.lines[#chat.lines + 1] = line
    adapter.add(line)
  end
  function chat.removeById(id)
    for i, e in ipairs(chat.entries) do
      if e.id == id then
        table.remove(chat.entries, i)
        table.remove(chat.lines, i)
        break
      end
    end
    rebuild()
  end
  function chat.removeByName(lname)
    for i = #chat.entries, 1, -1 do
      local e = chat.entries[i]
      if e.name and e.kind ~= "system" and e.kind ~= "notif" and tostring(e.name):lower() == lname then
        table.remove(chat.entries, i)
        table.remove(chat.lines, i)
      end
    end
    rebuild()
  end
  function chat.close() pcall(function() dlg.dismiss() end) end

  dlg.setOnDismissListener(DialogInterface.OnDismissListener{onDismiss = function()
    pcall(function()
      local t = input.getText().toString()
      if t ~= "" then prefs.edit().putString("draft_" .. chat.id, t).commit()
      else prefs.edit().remove("draft_" .. chat.id).commit() end
    end)
    stopRec(true)
    stopAllAudio()
    chat.callMode = false
    if state.chat == chat then state.chat = nil end
    if state.running and not chat.noList then openList() end
  end})

  -- Mi rol en este chat (para saber si puedo borrar mensajes de otros)
  request("GET", "/api/rooms?action=info&room=" .. c.id, nil, function(code, o, err)
    if not err and o and o.optBoolean("ok") then chat.role = o.optString("role", "member") end
  end)

  ---------------------------------------------------- respuestas
  local function clearReply()
    chat.replyTo = nil
    input.setHint("Escribe tu mensaje")
  end

  local function setReply(e)
    local q
    if e.kind == "audio" then
      q = "mensaje de voz"
    else
      q = oneLine(e.text)
      local pos = q:find('"): ', 1, true)
      if q:sub(1, 15) == "En respuesta a " and pos then q = q:sub(pos + 4) end
      q = short(q, 60)
    end
    chat.replyTo = {name = e.name, quote = q}
    input.setHint("Respondiendo a " .. e.name .. ": " .. q)
    toast("Respondiendo a " .. e.name .. ". Escribe tu mensaje y pulsa Enviar.")
    pcall(function() input.requestFocus() end)
  end

  ---------------------------------------------------- reenviar e ignorar
  local function forwardText(e)
    local labels, list = {}, {}
    for _, ch in ipairs(state.chats) do
      list[#list + 1] = ch
      labels[#labels + 1] = ((ch.type == "dm") and "Chat con " or "") .. ch.title
    end
    if #labels == 0 then toast("No hay chats disponibles para reenviar.") return end
    pick("Reenviar a...", labels, function(i)
      local target = list[i]
      local body = cut("Reenviado de " .. tostring(e.name) .. ": " .. oneLine(e.text), 480)
      request("POST", "/api/send", {room = target.id, text = body}, function(code, o, err)
        if err then toast(err) return end
        if not o.optBoolean("ok") then toast(errText(o)) return end
        toast("Mensaje reenviado a " .. target.title .. ".")
        if target.id == chat.id then doPoll() end
      end)
    end)
  end

  local function ignoreUser(name)
    confirm("Ignorar a " .. name, "No verás ni escucharás sus mensajes en tu teléfono. Los demás seguirán viéndolos. Puedes dejar de ignorarlo en Ajustes. ¿Continuar?", function()
      if not isIgnored(name) then listToggle("ignored", name:lower(), "|") end
      chat.removeByName(name:lower())
      toast("Ahora ignoras a " .. name .. ".")
    end)
  end

  local function reportMessage(e)
    ask("Reportar mensaje de " .. tostring(e.name), {"Motivo (opcional)"}, function(v)
      request("POST", "/api/report", {kind = "message", room = chat.id, id = e.id, reason = v[1]}, function(code, o, err)
        if err then toast(err) return end
        if not o.optBoolean("ok") then toast(errText(o)) return end
        toast("Reporte enviado al administrador.")
      end)
    end)
  end

  ---------------------------------------------------- menú de un mensaje
  local function messageMenu(e)
    if not e or e.kind == "notif" or e.kind == "system" or not e.id then return end
    local mine = (e.name == state.name)
    local canDelete = mine or chat.role == "owner" or chat.role == "admin"
    local labels, acts = {}, {}
    local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
    if e.kind == "audio" then
      add("Reproducir mensaje de voz", function() playAudio(chat.id, e.id) end)
    end
    add("Responder", function() setReply(e) end)
    if e.kind == "text" and e.text then
      add("Copiar texto", function() copyText(e.text) end)
      add("Reenviar a otro chat", function() forwardText(e) end)
      add("Compartir con otras aplicaciones", function() shareText(tostring(e.name) .. ": " .. e.text) end)
    end
    add("Ver detalles del mensaje", function()
      message("Detalles", "Enviado por " .. tostring(e.name) .. " el " .. fmtDateTime(e.ts) .. ". Tipo: " .. ((e.kind == "audio") and "mensaje de voz" or "texto") .. ".")
    end)
    if e.kind == "text" and e.text then
      add("Destacar mensaje", function()
        local list = getStars()
        list[#list + 1] = {room = chat.id, name = clean1(e.name), text = clean1(e.text)}
        while #list > MAX_STARS do table.remove(list, 1) end
        setStars(list)
        toast("Mensaje destacado. Lo encuentras en Ajustes.")
      end)
    end
    if not mine then
      if chat.type ~= "dm" then
        add("Escribirle en privado a " .. tostring(e.name), function()
          doPost({action = "dm", user = e.name}, nil, function(o)
            chat.noList = true
            chat.close()
            state.running = true
            openChat({id = o.optString("id"), name = e.name, type = "dm"})
          end)
        end)
      end
      add("Ver perfil de " .. tostring(e.name) .. ", bloquear o reportar", function() personMenu(e.name, function() end) end)
      add("Reportar este mensaje al administrador", function() reportMessage(e) end)
      add("Ignorar a " .. tostring(e.name) .. " (solo en mi teléfono)", function() ignoreUser(e.name) end)
    end
    if canDelete then
      add("Eliminar mensaje", function()
        confirm("Eliminar mensaje", "¿Eliminar este mensaje para todos?", function()
          request("POST", "/api/msg", {room = chat.id, id = e.id}, function(code, o, err)
            if err then toast(err) return end
            if not o.optBoolean("ok") then toast(errText(o)) return end
            chat.removeById(e.id)
            toast("Mensaje eliminado")
          end)
        end)
      end)
    end
    pick("Mensaje de " .. tostring(e.name), labels, function(i) acts[i]() end)
  end

  ---------------------------------------------------- modo llamada de voz (dentro de la app)
  local function setCallMode(on)
    chat.callMode = on
    if on then
      callBtn.setText("Terminar llamada de voz")
      toast("Llamada de voz activada. Los mensajes de voz que lleguen suenan solos. Pulsa Hablar para responder.")
    else
      stopAllAudio()
      callBtn.setText("Iniciar llamada de voz")
      toast("Llamada terminada.")
    end
    if not rec then recBtn.setText(on and "Hablar" or "Grabar mensaje de voz") end
  end

  ---------------------------------------------------- grabación
  local function resetRecUi()
    recBtn.setText(chat.callMode and "Hablar" or "Grabar mensaje de voz")
    cancel.setVisibility(8)
  end

  local function finishRec()
    local path, secs = stopRec(false)
    resetRecUi()
    if not path then return end
    toast(chat.callMode and "Enviando" or "Enviando mensaje de voz")
    sendAudioFile(chat.id, path, secs, function(code, o, err)
      if err then toast(err) return end
      if not o.optBoolean("ok") then toast(errText(o)) return end
      toast(chat.callMode and "Enviado" or "Mensaje de voz enviado")
      doPoll()
    end)
  end

  ---------------------------------------------------- eventos de la lista de mensajes
  -- Toque: audio = reproducir, aviso de llamada = unirse, texto = menú del mensaje
  lv.setOnItemClickListener(AdapterView.OnItemClickListener{onItemClick = function(parent, view, pos, id)
    local e = chat.entries[pos + 1]
    if not e then return end
    if e.kind == "audio" then
      playAudio(chat.id, e.id)
    elseif e.kind == "text" and e.text and e.name ~= state.name and e.text:find(CALL_MARK, 1, true) and not chat.callMode then
      confirm("Llamada de voz", "¿Quieres unirte a la llamada de voz de " .. tostring(e.name) .. "?", function() setCallMode(true) end)
    elseif e.kind == "text" then
      messageMenu(e)
    end
  end})

  -- Pulsación larga: menú del mensaje (también para audios)
  lv.setOnItemLongClickListener(AdapterView.OnItemLongClickListener{onItemLongClick = function(parent, view, pos, id)
    messageMenu(chat.entries[pos + 1])
    return true
  end})

  ---------------------------------------------------- botones
  send.setOnClickListener(View.OnClickListener{onClick = function()
    local text = input.getText().toString()
    if text == "" then toast("Escribe un mensaje primero.") return end
    local full = text
    local reply = chat.replyTo
    if reply then full = 'En respuesta a ' .. reply.name .. ' ("' .. reply.quote .. '"): ' .. text end
    if ulen(full) > MAX_MSG then
      toast("El mensaje es demasiado largo (" .. ulen(full) .. " de " .. MAX_MSG .. " caracteres). Acórtalo.")
      return
    end
    input.setText("")
    request("POST", "/api/send", {room = chat.id, text = full}, function(code, o, err)
      local failed = err or not o.optBoolean("ok")
      if failed then
        toast(err or errText(o))
        if input.getText().toString() == "" then input.setText(text) end
        return
      end
      if reply then clearReply() end
      doPoll()
    end)
  end})

  recBtn.setOnClickListener(View.OnClickListener{onClick = function()
    if rec then finishRec() return end
    stopAllAudio() -- para no grabar lo que esté sonando
    if startRec() then
      recBtn.setText(chat.callMode and "Terminar y enviar" or "Detener y enviar mensaje de voz")
      cancel.setVisibility(0)
      toast(chat.callMode and "Hablando. Pulsa de nuevo para enviar." or "Grabando. Pulsa de nuevo para enviar.")
      local myId = recId
      local limit = chat.callMode and MAX_CALL_SECONDS or MAX_REC_SECONDS
      handler.postDelayed(Runnable{run = function()
        if rec and recId == myId then toast("Límite de tiempo alcanzado") finishRec() end
      end}, limit * 1000)
    end
  end})

  cancel.setOnClickListener(View.OnClickListener{onClick = function()
    stopRec(true)
    resetRecUi()
    toast("Grabación descartada")
  end})

  callBtn.setOnClickListener(View.OnClickListener{onClick = function()
    if chat.callMode then setCallMode(false) return end
    confirm("Iniciar llamada de voz", "Se avisará a este chat que iniciaste una llamada de voz y se activará el modo llamada: los mensajes de voz que lleguen suenan solos y tú hablas con el botón Hablar. ¿Continuar?", function()
      setCallMode(true)
      request("POST", "/api/send", {room = chat.id, text = state.name .. " inició una llamada de voz. Pulsa " .. CALL_MARK .. "."}, function(code, o, err)
        if err then toast(err) return end
        if not o.optBoolean("ok") then toast(errText(o)) return end
        doPoll()
      end)
    end)
  end})

  phrasesBtn.setOnClickListener(View.OnClickListener{onClick = function()
    local ph = getPhrases()
    if #ph == 0 then toast("No tienes frases rápidas. Agrégalas en Ajustes.") return end
    pick("Frases rápidas", ph, function(i)
      local cur = input.getText().toString()
      input.setText(cur .. ((cur ~= "") and " " or "") .. ph[i])
      pcall(function() input.setSelection(input.getText().length()) end)
      toast("Frase agregada. Pulsa Enviar.")
    end)
  end})

  local function chatSearch()
    ask("Buscar en este chat", {"Palabra o frase"}, function(v)
      local q = v[1]:lower()
      if q == "" then return end
      local labels, idxs = {}, {}
      for i, l in ipairs(chat.lines) do
        if l:lower():find(q, 1, true) then labels[#labels + 1] = l; idxs[#idxs + 1] = i end
      end
      if #labels == 0 then toast("No se encontró ese texto en los mensajes cargados.") return end
      pick("Resultados (" .. #labels .. ")", labels, function(i)
        pcall(function() lv.setSelection(idxs[i] - 1) end)
        toast(labels[i])
      end)
    end)
  end

  moreBtn.setOnClickListener(View.OnClickListener{onClick = function()
    local labels, acts = {}, {}
    local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
    add("Buscar en este chat", chatSearch)
    add("Ir al último mensaje", function() pcall(function() lv.setSelection(adapter.getCount() - 1) end) end)
    add("Copiar toda la conversación", function()
      if #chat.lines == 0 then toast("No hay mensajes.") return end
      copyText(table.concat(chat.lines, "\n"), "Se copiaron " .. #chat.lines .. " mensajes.")
    end)
    add(isMutedChat(chat.id) and "Activar notificaciones de este chat" or "Silenciar notificaciones de este chat", function()
      local on = listToggle("mutedchats", chat.id, ";")
      toast(on and "Chat silenciado." or "Notificaciones activadas.")
    end)
    add(toggleLabel("Reproducir audios nuevos automáticamente", "autoplay", false), function()
      toggle("autoplay", false)
      toast("Reproducción automática: " .. yn(pb("autoplay", false)))
    end)
    if chat.replyTo then add("Cancelar la respuesta a " .. chat.replyTo.name, function() clearReply() toast("Respuesta cancelada.") end) end
    add("Actualizar mensajes ahora", function() doPoll() end)
    pick("Más opciones", labels, function(i) acts[i]() end)
  end})

  settings.setOnClickListener(View.OnClickListener{onClick = function() openSettings(chat) end})
  back.setOnClickListener(View.OnClickListener{onClick = function() dlg.dismiss() end})

  showDialog(dlg)
  doPoll()
end

------------------------------------------------------------ avisos del administrador
function openNotices()
  request("GET", "/api/notices", nil, function(code, o, err)
    state.newNotices = 0
    if err then toast(err) openList() return end
    if not o.optBoolean("ok") then toast(errText(o)) openList() return end
    local arr = o.optJSONArray("notices")
    local labels, items = {}, {}
    for i = 0, arr.length() - 1 do
      local n = arr.getJSONObject(i)
      items[#items + 1] = n
      local fechaTxt = os.date("%d/%m %H:%M", math.floor(n.optLong("ts") / 1000))
      labels[#labels + 1] = n.optString("title") .. ": " .. short(n.optString("text"), 60) .. ". " .. fechaTxt
    end
    if #labels == 0 then toast("No hay avisos del administrador.") openList() return end
    pick("Avisos del administrador", labels, function(i)
      local n = items[i]
      message("Aviso del administrador", n.optString("title") .. ". " .. n.optString("text"), openNotices)
    end, openList)
  end)
end

------------------------------------------------------------ ajustes de la cuenta y la app
local SPEEDS = {"1.0", "1.25", "1.5", "2.0"}

local function nextSpeed()
  local cur = prefs.getString("speed", "1.0")
  local idx = 1
  for i, s in ipairs(SPEEDS) do if s == cur then idx = i end end
  idx = (idx % #SPEEDS) + 1
  prefs.edit().putString("speed", SPEEDS[idx]).commit()
end

local function managePhrases(back)
  local ph = getPhrases()
  local labels = {"Agregar una frase nueva"}
  for _, p in ipairs(ph) do labels[#labels + 1] = p end
  pick("Frases rápidas (" .. #ph .. ")", labels, function(i)
    if i == 1 then
      ask("Frase nueva", {"Texto de la frase"}, function(v)
        local t = oneLine(v[1]):match("^%s*(.-)%s*$")
        if t == "" then toast("Escribe la frase.") managePhrases(back) return end
        local cur = getPhrases()
        cur[#cur + 1] = cut(t, 200)
        setPhrases(cur)
        toast("Frase agregada.")
        managePhrases(back)
      end, {back = function() managePhrases(back) end})
    else
      local idx = i - 1
      confirm("Eliminar frase", "¿Eliminar la frase: " .. ph[idx] .. "?", function()
        local cur = getPhrases()
        table.remove(cur, idx)
        setPhrases(cur)
        toast("Frase eliminada.")
        managePhrases(back)
      end, function() managePhrases(back) end)
    end
  end, back)
end

local function manageIgnored(back)
  local list = listGet("ignored", "|")
  if #list == 0 then
    message("Usuarios ignorados", "No estás ignorando a nadie. Para ignorar a alguien, toca uno de sus mensajes y elige Ignorar.", back)
    return
  end
  pick("Usuarios ignorados (" .. #list .. ")", list, function(i)
    local n = list[i]
    confirm("Dejar de ignorar", "¿Volver a ver los mensajes de " .. n .. "?", function()
      listToggle("ignored", n, "|")
      toast("Ya verás sus mensajes.")
      manageIgnored(back)
    end, function() manageIgnored(back) end)
  end, back)
end

function openAppSettings()
  local labels, acts = {}, {}
  local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
  local function again() openAppSettings() end

  add("Cambiar mi nombre de usuario", function()
    ask("Cambiar nombre de usuario", {"Nuevo nombre", "Tu contraseña actual"}, function(v)
      request("POST", "/api/account", {action = "rename", name = v[1], password = v[2]}, function(code, o, err)
        if err then toast(err) openAppSettings() return end
        if not o.optBoolean("ok") then toast(errText(o)) openAppSettings() return end
        state.token = o.optString("token")
        state.name = o.optString("name")
        prefs.edit().putString("token", state.token).putString("name", state.name).commit()
        message("Nombre cambiado", "Ahora te llamas " .. state.name .. ". Tus mensajes anteriores conservan el nombre viejo.", openAppSettings)
      end)
    end, {back = openAppSettings, password = true, passFrom = 2})
  end)

  add("Cambiar mi contraseña", function()
    ask("Cambiar contraseña", {"Contraseña actual", "Contraseña nueva (mínimo 6 caracteres)"}, function(v)
      request("POST", "/api/account", {action = "password", old = v[1], new = v[2]}, function(code, o, err)
        if err then toast(err) openAppSettings() return end
        if not o.optBoolean("ok") then toast(errText(o)) openAppSettings() return end
        if pb("savepw", true) then prefs.edit().putString("pw", v[2]).commit() end
        message("Contraseña cambiada", "Tu contraseña se cambió correctamente.", openAppSettings)
      end)
    end, {back = openAppSettings, password = true, passFrom = 1})
  end)

  add("Ver mi contraseña (guardada en este dispositivo)", function()
    local pw = prefs.getString("pw", "")
    if pw ~= "" then message("Tu contraseña", "Tu contraseña es: " .. pw .. "\nSolo se guarda en este teléfono.", openAppSettings)
    else message("Tu contraseña", "No hay contraseña guardada en este dispositivo. Activa \"Guardar mi contraseña\" y vuelve a iniciar sesión.", openAppSettings) end
  end)

  add(toggleLabel("Guardar mi contraseña en este dispositivo", "savepw", true), function()
    toggle("savepw", true)
    if not pb("savepw", true) then prefs.edit().remove("pw").commit() end
    openAppSettings()
  end)
  add(toggleLabel("Mostrar la contraseña al escribirla", "showpw", false), function() toggle("showpw", false) openAppSettings() end)
  add(toggleLabel("Notificaciones en segundo plano", "bg", true), function() toggle("bg", true) openAppSettings() end)
  add(toggleLabel("Avisar de mensajes del chat General", "notifyGeneral", false), function() toggle("notifyGeneral", false) openAppSettings() end)
  add(toggleLabel("Anunciar los mensajes nuevos", "speak", true), function() toggle("speak", true) openAppSettings() end)
  add(toggleLabel("Avisar siempre cuando escriban mi nombre", "mentions", true), function() toggle("mentions", true) openAppSettings() end)
  add(toggleLabel("Mostrar la hora de cada mensaje", "showtime", false), function() toggle("showtime", false) openAppSettings() end)
  add(toggleLabel("Reproducir audios nuevos automáticamente", "autoplay", false), function() toggle("autoplay", false) openAppSettings() end)
  add("Velocidad de los mensajes de voz: " .. prefs.getString("speed", "1.0") .. "x. Toca para cambiarla", function() nextSpeed() openAppSettings() end)

  add("Frases rápidas (" .. #getPhrases() .. ")", function() managePhrases(again) end)
  add("Usuarios ignorados (" .. #listGet("ignored", "|") .. ")", function() manageIgnored(again) end)
  add("Mi descripción (acerca de mí)", function() editBio(again) end)
  add("Personas bloqueadas", function() manageBlocked(again) end)
  add("Mensajes destacados (" .. #getStars() .. ")", function() manageStars(again) end)
  add("Escribir al administrador", function() contactAdmin(again) end)
  add("Novedades de esta versión", function() showNews(again) end)
  add("Probar la conexión con los servidores", function() testServers(again) end)

  add("Ver las reglas de la comunidad", function()
    request("GET", "/api/info", nil, function(code, o, err)
      if err then toast(err) openAppSettings() return end
      local t = {}
      local arr = o.optJSONArray("rules")
      if arr then for i = 0, arr.length() - 1 do t[#t + 1] = (i + 1) .. ". " .. arr.getString(i) end end
      message("Reglas de la comunidad", table.concat(t, "\n"), openAppSettings)
    end)
  end)
  add("Eliminar audios guardados y liberar espacio", function() cleanAudios(openAppSettings) end)

  pick("Ajustes", labels, function(i) acts[i]() end, openList)
end

------------------------------------------------------------ lista de chats y grupos públicos
local function newGroup()
  ask("Nuevo grupo", {"Nombre del grupo", "Descripción (opcional)"}, function(v)
    pick("¿Quién puede unirse al grupo?", {"Público: cualquiera puede verlo y unirse", "Privado: solo entran las personas que tú agregues"}, function(i)
      doPost({action = "create", name = v[1], desc = v[2], privacy = (i == 2) and "private" or "public"}, nil, function(o)
        state.running = true
        openChat({id = o.optString("id"), name = o.optString("name"), type = "group"})
      end)
    end, openList, "Cancelar")
  end, {back = openList})
end

local function joinPublic(id, name)
  doPost({action = "join", room = id}, nil, function()
    state.running = true
    openChat({id = id, name = name, type = "group"})
  end)
end

-- Directorio de grupos públicos: se muestran todos directamente (los privados nunca aparecen).
-- La primera opción permite buscar por una palabra.
local function openPublicGroups(q)
  q = q or ""
  request("GET", "/api/rooms?action=discover&q=" .. Uri.encode(q), nil, function(code, o, err)
    if err then toast(err) openList() return end
    if not o.optBoolean("ok") then toast(errText(o)) openList() return end
    local arr = o.optJSONArray("groups")
    local labels, groups = {"Buscar por una palabra..."}, {false}
    for i = 0, arr.length() - 1 do
      local g = arr.getJSONObject(i)
      if g.optString("privacy") ~= "private" then
        local desc = g.optString("desc")
        groups[#groups + 1] = {id = g.optString("id"), name = g.optString("name"), member = g.optBoolean("member")}
        labels[#labels + 1] = g.optString("name") .. ", " .. g.optInt("count") .. " miembros" .. (g.optBoolean("member") and ", ya eres miembro" or "") .. (desc ~= "" and (". " .. short(desc, 60)) or "")
      end
    end
    local n = #labels - 1
    local title = (q ~= "") and ("Grupos públicos con \"" .. q .. "\" (" .. n .. ")") or ("Grupos públicos (" .. n .. ")")
    if n == 0 then toast("No hay grupos públicos" .. ((q ~= "") and " con esa palabra." or " todavía.")) end
    pick(title, labels, function(i)
      if i == 1 then
        ask("Buscar grupos públicos", {"Palabra a buscar"}, function(v) openPublicGroups(v[1]) end, {back = function() openPublicGroups(q) end})
      else
        local g = groups[i]
        if g.member then
          state.running = true
          openChat({id = g.id, name = g.name, type = "group"})
        else
          joinPublic(g.id, g.name)
        end
      end
    end, openList)
  end)
end

local function leaveChat(ch)
  local what = (ch.type == "dm") and "Eliminar este chat de mi lista" or "Salir del grupo"
  confirm(what, "¿" .. what .. ": " .. ch.title .. "?", function()
    doPost({action = "leave", room = ch.id}, (ch.type == "dm") and "Chat eliminado de tu lista." or "Saliste del grupo.", openList)
  end, openList)
end

local function leaveMenu()
  local labels, list = {}, {}
  for _, ch in ipairs(state.chats) do
    if ch.id ~= "general" then
      list[#list + 1] = ch
      labels[#labels + 1] = (ch.type == "dm" and "Chat con " or "Grupo ") .. ch.title
    end
  end
  if #labels == 0 then toast("No tienes grupos ni chats de los que salir.") openList() return end
  pick("¿De cuál quieres salir?", labels, function(i) leaveChat(list[i]) end, openList)
end

-- Menú de un chat de la lista (pulsación larga)
local function chatMenu(ch)
  local labels, acts = {}, {}
  local function add(l, f) labels[#labels + 1] = l; acts[#acts + 1] = f end
  add(isPinned(ch.id) and "Quitar de fijados" or "Fijar arriba", function()
    local on = listToggle("pinned", ch.id, ";")
    toast(on and "Chat fijado arriba." or "Chat desfijado.")
    openList()
  end)
  add(isMutedChat(ch.id) and "Activar notificaciones de este chat" or "Silenciar notificaciones de este chat", function()
    local on = listToggle("mutedchats", ch.id, ";")
    toast(on and "Chat silenciado." or "Notificaciones activadas.")
    openList()
  end)
  if ch.id ~= "general" then
    add((ch.type == "dm") and "Eliminar este chat de mi lista" or "Salir del grupo", function() leaveChat(ch) end)
  end
  pick(ch.title, labels, function(i) acts[i]() end, openList)
end

local MAX_INLINE_PUBLIC = 8

function openList()
  request("GET", "/api/rooms?action=list&seen=" .. Uri.encode(prefs.getString("seen", "")), nil, function(code, o, err)
    if not state.running then return end
    local ok = (not err) and o ~= nil and o.optBoolean("ok")
    if not ok then toast(err or (o and errText(o)) or "No se pudo cargar la lista.") end

    -- chats propios (los fijados van primero)
    local pinnedRows, otherRows = {}, {}
    if ok then
      local arr = o.optJSONArray("chats")
      for i = 0, arr.length() - 1 do
        local c = arr.getJSONObject(i)
        local chat = {id = c.optString("id"), name = c.optString("name"), type = c.optString("type"), members = jarr(c.optJSONArray("members"))}
        local title = chat.name
        if chat.type == "dm" then
          title = ""
          for _, m in ipairs(chat.members) do if m:lower() ~= state.name:lower() then title = m end end
          if title == "" then title = "Chat privado" end
        end
        chat.title = title
        local label = title
        if chat.type == "dm" then label = "Chat con " .. title end
        local unread = c.optInt("unread")
        if unread > 0 then label = label .. ", " .. unread .. " sin leer" end
        local last = c.optJSONObject("last")
        if last then
          local who = last.optString("name")
          if who == state.name then who = "Tú" end
          label = label .. ". " .. who .. ": " .. short(last.optString("text"), 40)
        end
        if isMutedChat(chat.id) then label = label .. ". Silenciado" end
        if isPinned(chat.id) then
          pinnedRows[#pinnedRows + 1] = {chat = chat, label = "Fijado: " .. label}
        else
          otherRows[#otherRows + 1] = {chat = chat, label = label}
        end
      end
    end
    local rows = {}
    for _, r in ipairs(pinnedRows) do rows[#rows + 1] = r end
    for _, r in ipairs(otherRows) do rows[#rows + 1] = r end
    state.chats = {}
    for _, r in ipairs(rows) do state.chats[#state.chats + 1] = r.chat end

    local function render(pubs)
      if not state.running then return end
      local labels, acts, rowChat = {}, {}, {}
      local function add(l, f, ch) labels[#labels + 1] = l; acts[#labels] = f; rowChat[#labels] = ch end
      add("Avisos del administrador" .. (state.newNotices > 0 and (", " .. state.newNotices .. " nuevos") or ""), openNotices)
      add("Nuevo grupo", newGroup)
      add("Personas: buscar y escribir en privado", openPeople)
      add("Ver y buscar grupos públicos", function() openPublicGroups("") end)
      add("Unirme con un código de invitación", joinWithCode)
      for _, r in ipairs(rows) do
        local chat = r.chat
        add(r.label, function() openChat(chat) end, chat)
      end
      if #pubs > 0 then
        add("Grupos públicos para unirte, sin tener que buscar:", nil)
        for i = 1, math.min(#pubs, MAX_INLINE_PUBLIC) do
          local g = pubs[i]
          add("Grupo público: " .. g.name .. ", " .. g.count .. " miembros" .. (g.desc ~= "" and (". " .. short(g.desc, 50)) or "") .. ". Toca para unirte", function() joinPublic(g.id, g.name) end)
        end
        if #pubs > MAX_INLINE_PUBLIC then
          add("Ver los " .. #pubs .. " grupos públicos", function() openPublicGroups("") end)
        end
      end
      add("Ajustes", openAppSettings)
      add("Actualizar lista", function() openList() end)
      add("Salir de un grupo o eliminar un chat", leaveMenu)
      add("Eliminar audios y liberar espacio", function() cleanAudios(openList) end)
      add("Cerrar sesión", function() logout("Sesión cerrada.") end)

      local lay = LinearLayout(ctx)
      lay.setOrientation(1)
      lay.setPadding(12, 12, 12, 12)
      lay.setBackgroundColor(0xFFEEEEEE)

      local header = TextView(ctx)
      header.setText("Mis chats - " .. state.name)
      header.setTextSize(20)
      header.setPadding(0, 0, 0, 12)
      lay.addView(header)

      local data = ArrayList()
      for _, l in ipairs(labels) do data.add(l) end
      local adapter = ArrayAdapter(ctx, android.R.layout.simple_list_item_1, data)
      local lv = ListView(ctx)
      lv.setAdapter(adapter)
      lay.addView(lv, LinearLayout.LayoutParams(-1, 0, 1))

      local btnRow = LinearLayout(ctx)
      btnRow.setOrientation(0)
      local closeBtn = Button(ctx)
      closeBtn.setText("Cerrar")
      btnRow.addView(closeBtn, LinearLayout.LayoutParams(0, -2, 1))
      lay.addView(btnRow)

      local b = AlertDialog.Builder(ctx)
      b.setView(lay)
      b.setCancelable(false)
      local dlg = b.create()
      state.dlg = dlg

      -- Cerrar el complemento solo ocurre con este botón (las notificaciones siguen en segundo plano)
      closeBtn.setOnClickListener(View.OnClickListener{onClick = function()
        state.running = false
        pcall(function() dlg.dismiss() end)
      end})

      dlg.setOnDismissListener(DialogInterface.OnDismissListener{onDismiss = function() state.listShown = false end})

      lv.setOnItemClickListener(AdapterView.OnItemClickListener{onItemClick = function(parent, view, pos, id)
        local act = acts[pos + 1]
        if act then
          pcall(function() dlg.dismiss() end)
          act()
        end
      end})

      -- Pulsación larga sobre un chat: fijar, silenciar, salir
      lv.setOnItemLongClickListener(AdapterView.OnItemLongClickListener{onItemLongClick = function(parent, view, pos, id)
        local ch = rowChat[pos + 1]
        if ch then
          pcall(function() dlg.dismiss() end)
          chatMenu(ch)
        end
        return true
      end})

      showDialog(dlg)
      state.listShown = true
    end

    -- grupos públicos que el servidor manda junto con la lista (sin los privados)
    local function readPubs(arr)
      local pubs = {}
      if arr then
        for i = 0, arr.length() - 1 do
          local g = arr.getJSONObject(i)
          if g.optString("privacy") ~= "private" and not g.optBoolean("member") and g.optString("id") ~= "general" then
            pubs[#pubs + 1] = {id = g.optString("id"), name = g.optString("name"), desc = g.optString("desc"), count = g.optInt("count")}
          end
        end
      end
      return pubs
    end

    local parr = ok and o.optJSONArray("publicGroups") or nil
    if ok and not parr then
      -- servidor sin ese dato: se pide el directorio aparte
      request("GET", "/api/rooms?action=discover&q=", nil, function(c2, o2, e2)
        if not e2 and o2 and o2.optBoolean("ok") then render(readPubs(o2.optJSONArray("groups"))) else render({}) end
      end)
    else
      render(readPubs(parr))
    end
  end)
end

------------------------------------------------------------ inicio de sesión
local function saveSession(o, password)
  state.token = o.optString("token")
  state.name = o.optString("name")
  prefs.edit().putString("token", state.token).putString("name", state.name).commit()
  if pb("savepw", true) and password and password ~= "" then prefs.edit().putString("pw", password).commit() end
end

local function afterLogin()
  state.running = true
  state.alive = true
  startLoop()
  if not pb("news4", false) then
    prefs.edit().putBoolean("news4", true).commit()
    showNews(openList)
  else
    openList()
  end
end

local function rulesDialog(o, after)
  local arr = o.optJSONArray("rules")
  local t = {}
  if arr then for i = 0, arr.length() - 1 do t[#t + 1] = (i + 1) .. ". " .. arr.getString(i) end end
  local b = AlertDialog.Builder(ctx)
  b.setTitle("Reglas de la comunidad")
  b.setMessage(table.concat(t, "\n"))
  b.setPositiveButton("Acepto", DialogInterface.OnClickListener{onClick = function() after() end})
  b.setCancelable(false)
  showDialog(b.create())
end

function startLogin(register)
  local lay = LinearLayout(ctx)
  lay.setOrientation(1)
  lay.setPadding(40, 20, 40, 20)
  local name = EditText(ctx)
  name.setHint("Nombre de usuario")
  local pass = EditText(ctx)
  pass.setHint("Contraseña")
  pass.setInputType(pb("showpw", false) and 145 or 129)
  lay.addView(name)
  lay.addView(pass)
  local b = AlertDialog.Builder(ctx)
  b.setTitle(register and "Crear cuenta" or "Iniciar sesión")
  b.setView(lay)
  b.setCancelable(false)
  b.setPositiveButton(register and "Registrarme" or "Entrar", DialogInterface.OnClickListener{onClick = function()
    local path = register and "/api/register" or "/api/login"
    local pw = pass.getText().toString()
    request("POST", path, {name = name.getText().toString(), password = pw}, function(code, o, err)
      if err then toast(err) startLogin(register) return end
      if not o.optBoolean("ok") then
        if code == 403 and isBan(o) then bannedScreen(errText(o)) return end
        toast(errText(o))
        startLogin(register)
        return
      end
      saveSession(o, pw)
      if register then rulesDialog(o, afterLogin) else afterLogin() end
    end)
  end})
  b.setNeutralButton(register and "Ya tengo cuenta" or "Crear cuenta nueva", DialogInterface.OnClickListener{onClick = function() startLogin(not register) end})
  b.setNegativeButton("Cerrar", nil)
  showDialog(b.create())
end

-- Inicio del plugin
if state.token ~= "" then afterLogin() else startLogin(false) end