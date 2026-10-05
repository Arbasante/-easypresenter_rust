# Respaldo en línea de ReadyShow

La opción está en **Herramientas → Respaldo en línea**. Respalda las tablas de
`cantos.db` (cantos, diapositivas, favoritos) y `biblias.db` (versiones, versiculos).
No incluye videos, PDFs, imágenes, fuentes ni configuración personal.

## Inicio de sesión desde ReadyShow

El usuario abre **Herramientas → Respaldo en línea → Iniciar sesión con Google**.
ReadyShow abre el navegador predeterminado, Google permite elegir una cuenta ya
iniciada y muestra los permisos de Drive. Al autorizar, ReadyShow recibe el código
en `127.0.0.1` (puerto dinámico), valida `state`, aplica PKCE y conecta el respaldo.
Los usuarios no necesitan Google Cloud Console, variables de entorno ni JSON.
La contraseña se introduce únicamente en Google; ReadyShow no la solicita.

Los tokens se mantienen en memoria y se renuevan durante la sesión actual.
Al reiniciar ReadyShow hay que pulsar de nuevo el botón de inicio de sesión.

## Configuración de la aplicación al compilar (desarrollador)

El cliente OAuth de escritorio identifica a **ReadyShow**, es común a sus usuarios
y debe configurarse una vez al preparar el ejecutable. Google Drive API y la
pantalla de consentimiento deben estar configuradas en ese proyecto.

`build.rs` incluye en el ejecutable los campos del cliente de escritorio. La fuente
se elige en este orden:

1. `READYSHOW_GOOGLE_CLIENT_ID` y, cuando corresponde, `READYSHOW_GOOGLE_CLIENT_SECRET`.
2. El JSON de escritorio indicado por `READYSHOW_GOOGLE_OAUTH_FILE`.
3. `data/google_oauth.json`, ya existente si se usó el importador de versiones anteriores.

Solo se incluyen `client_id` y `client_secret` del cliente **installed**. No se
incluyen tokens de usuarios, cuentas de servicio, claves privadas, clientes web
ni URLs del archivo. La configuración generada está en `OUT_DIR`, bajo `target/`,
y sus valores no se imprimen en los mensajes de compilación. La fuente local
permanece excluida de Git. Los clientes de aplicaciones nativas se consideran
públicos: el campo `client_secret` de un cliente de escritorio distribuido no
puede tratarse como un secreto confidencial ni reutilizarse como credencial de servidor.

Ejecutar `cargo run --release` desde este repositorio incluye automáticamente el
cliente presente en `data/google_oauth.json`. Para entregar la aplicación a otro
equipo basta el ejecutable empaquetado; ese equipo no necesita el JSON original.
Las variables y el JSON local siguen siendo una alternativa de desarrollo para
compilaciones sin cliente incluido. La configuración incluida tiene prioridad.
Una compilación sin cliente permite usar las funciones locales, pero informa que
el desarrollador debe habilitar Google Drive si se intenta iniciar sesión.

### Instaladores generados en GitHub Actions

El workflow `.github/workflows/build.yml` obtiene el cliente de escritorio de los
secretos del repositorio y lo incluye en los instaladores de Linux y Windows:

1. En Google Cloud, habilitar **Google Drive API**, configurar la pantalla de
   consentimiento y crear un cliente OAuth de tipo **Aplicación de escritorio**.
   Si la aplicación está en pruebas, añadir las cuentas que la probarán como
   usuarios de prueba.
2. En GitHub, abrir **Settings → Secrets and variables → Actions → New repository
   secret** y crear `READYSHOW_GOOGLE_CLIENT_ID` y
   `READYSHOW_GOOGLE_CLIENT_SECRET` con los valores `client_id` y `client_secret`
   del JSON descargado de Google. No subir ese JSON al repositorio.
3. Ejecutar nuevamente **Build Installers** desde la pestaña **Actions**, descargar
   el nuevo instalador e instalarlo en el equipo de destino.

El JSON local ignorado por Git no llega al runner de GitHub. Sin el secreto del
cliente, este workflow falla al validar el `client_id` durante la compilación;
así se evita entregar otro instalador sin respaldo en línea. Los paquetes ya
descargados no se actualizan al configurar los secretos: hay que recompilarlos.
Firefox puede abrir el inicio de sesión como navegador predeterminado; este
mensaje de cliente ausente se resuelve en la compilación del instalador.

## Permisos y bloqueo de Google durante pruebas

Se solicita `drive.file`, para operar los archivos creados por ReadyShow. Utilizar
el mismo proyecto/cliente OAuth en los distintos equipos permite restaurar esos
respaldos. No se descubren automáticamente carpetas ajenas a ese cliente.

El mensaje de Google «la aplicación está en pruebas y solo pueden acceder testers»
se resuelve en la configuración del proyecto del desarrollador: autorizar la
cuenta como usuario de prueba, o publicar la aplicación y completar lo que Google
requiera. Cambiar la UI o abrir otro navegador no elimina esa restricción. Los
usuarios finales no tienen que configurar su propio proyecto.

## Migración

La rutina `online_backup::migrate` inspecciona `PRAGMA table_info` dentro de una
transacción `IMMEDIATE`. Se ejecuta desde `AppState::new()` antes de crear incluso
la ventana splash de Slint. Añade únicamente columnas faltantes y completa las
tablas auxiliares, también si existe un esquema parcialmente migrado.

Los archivos `migrations/cantos_sync.sql` y `migrations/biblias_sync.sql` definen
las tablas, índices y triggers idempotentes. Los `ALTER TABLE` y el registro del
respaldo inicial se ejecutan desde Rust; los scripts solos no migran las columnas.

Cada tabla principal recibe, cuando falta:

```sql
ALTER TABLE cantos ADD COLUMN updated_at TIMESTAMP NOT NULL DEFAULT 0;
UPDATE cantos SET updated_at = ?; -- milisegundos UTC de la migración
ALTER TABLE cantos ADD COLUMN is_deleted INTEGER NOT NULL DEFAULT 0
    CHECK (is_deleted IN (0, 1));
```

Se aplica lo mismo a diapositivas, favoritos, versiones y versiculos. SQLite no
permite `DEFAULT CURRENT_TIMESTAMP` en `ALTER TABLE ADD COLUMN`; por eso se añade
con un valor constante y se inicializan las filas existentes en la misma
transacción. Las fechas ya presentes y la marca de sincronización existente se
conservan. `last_sync_timestamp` empieza en `0` en una base nueva para el respaldo.

SQLite guarda `updated_at` como entero de milisegundos UTC. Los triggers asignan
un reloj monótono por base (`MAX(clock + 1, hora_actual)`), también si el reloj del
sistema retrocede o hay varias escrituras en un milisegundo.

`sync_metadata` contiene `last_sync_timestamp`, `clock`, `suppress`, `remote_folder`
y `local_instance`. `sync_changes` conserva JSON de los cambios y los borrados;
`sync_versions` conserva la última fecha por tabla/ID, incluso después de borrar.
Las filas recién migradas se registran inicialmente con versión local `0`, para
permitir restaurar un respaldo anterior sobre los datos de una instalación nueva;
conservan su fecha real en `updated_at` y el diario inicial. Las escrituras locales
posteriores y las restauraciones asignan una versión conocida efectiva.

Si algo falla, rusqlite revierte automáticamente la transacción. Las bases
existentes nunca se sustituyen por semillas durante el arranque: una comprobación
de integridad fallida aborta el inicio y conserva el archivo. Las semillas solo se
copian cuando falta el archivo. Cada base tiene su propia transacción; si la segunda
falla, los cambios de esquema de la primera ya confirmados permanecen válidos.

## Respaldo y restauración

El worker se crea con `tokio::spawn` en un runtime dedicado. SQLite, la generación
de JSON y la actualización de modelos usan `spawn_blocking`; las solicitudes
HTTP son asíncronas. No se comparte una conexión SQLite entre hilos.

Al iniciar sesión crea, si faltan, `Backup_ReadyShow/cantos` y
`Backup_ReadyShow/biblias`, y realiza el primer respaldo. Cada 600 segundos consulta
el diario por `timestamp > last_sync_timestamp`. La instantánea usa un límite
superior obtenido en la misma transacción de lectura. Los cambios posteriores a
ese límite permanecen pendientes. Antes de confirmar la marca se verifica también
la identidad local de la base, para detectar su reemplazo durante una subida. La marca se actualiza solo tras confirmar la
subida; errores de red se reintentan en el siguiente intervalo. Una respuesta
perdida puede producir un archivo duplicado, pero su importación es idempotente.

Al cambiar de carpeta destino/cuenta, el primer respaldo contiene todos los
registros actuales y las marcas de borrado conservadas, aunque se hayan eliminado
incrementales locales ya confirmados.

Los nombres son `cantos_delta_<timestamp_ms_con_ceros>_<aleatorio>.json` y su
equivalente de Biblias. Se utiliza el timestamp numérico del contenido para
ordenar la restauración. La lista de archivos está paginada.

**Restaurar datos en este equipo** inicia OAuth si hace falta, descarga los JSON
de cada subcarpeta, valida formato/tablas/columnas y aplica:

```sql
INSERT INTO cantos (id, titulo, tono, categoria, updated_at, is_deleted)
VALUES (?, ?, ?, ?, ?, ?)
ON CONFLICT(id) DO UPDATE SET
    titulo = excluded.titulo,
    tono = excluded.tono,
    categoria = excluded.categoria,
    updated_at = excluded.updated_at,
    is_deleted = excluded.is_deleted;
```

Aplica una versión si su `updated_at` supera la versión local conocida. Las
filas recién migradas sin cambios locales pueden aceptar un respaldo anterior
a la migración del equipo destino. También se mantiene la compatibilidad con
respaldos anteriores que usaban `updated_at=1` para sus datos iniciales. Los
borrados admiten `is_deleted: true` o `1`, eliminan la fila y conservan su marca
para impedir que otro delta antiguo la resucite. Una restauración aceptada elimina los cambios locales pendientes anteriores
para ese ID, para que una instantánea inicial no vuelva a sobrescribir lo restaurado.
Una referencia foránea inválida revierte la transacción. La UI vuelve a cargar canciones, favoritos y Biblias al
terminar. La mezcla es transaccional **por base**, no entre las dos bases: si falla
Biblias después de restaurar Cantos, Cantos permanece restaurada y la UI se
actualiza también en ese caso. Repetir la operación es seguro.

## Límites del modelo

La mezcla usa los IDs originales solicitados y gana la fecha más reciente. Dos
equipos que creen registros distintos con el mismo ID pueden colisionar; no es
un algoritmo para edición concurrente entre equipos con identidades globales.
La fecha de los equipos debe estar razonablemente sincronizada. Fechas idénticas
conservan la versión local, salvo la compatibilidad con respaldos iniciales
que usaban la marca `1`. Las restricciones únicas (por ejemplo, nombre de
versión bíblica) siguen vigentes y un conflicto revierte la mezcla de esa base.

Para grandes historiales se descargan y guardan los deltas de una base en memoria
antes de mezclarla. No se implementa compactación de los archivos remotos. Las
carpetas duplicadas se notifican para evitar seleccionar una al azar. Los errores
se muestran en la vista; no se registran tokens ni códigos OAuth.

## Validación

`cargo check` compila Rust y Slint. `cargo test online_backup::tests` verifica
migración, conservación de escrituras durante una subida, replay idempotente,
borrados y rollback sobre bases temporales. La prueba con Google real requiere
el cliente OAuth configurado y una cuenta autorizada: probar primer respaldo,
modificación/borrado, siguiente respaldo y restauración desde otro equipo.

Referencias oficiales:
- [Cliente OAuth para aplicaciones de escritorio](https://developers.google.com/identity/protocols/oauth2/native-app)
- [Scopes de Drive](https://developers.google.com/workspace/drive/api/guides/api-specific-auth)
- [Subidas multipart](https://developers.google.com/workspace/drive/api/guides/manage-uploads)
- [OAuth2 Rust con PKCE y cliente asíncrono](https://docs.rs/oauth2/latest/oauth2/)
