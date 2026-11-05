# ReadyShow: PWA de mando remoto

La aplicación autónoma para Android ahora es un proyecto **nativo Kotlin** en `../../readyshow-android` (carpeta hermana de este repositorio). Esta PWA se mantiene para **controlar la aplicación de escritorio por WiFi**. Las pantallas de eventos, planificaciones, notas, tareas, biblioteca local y ajustes se trasladaron a Android.

## Usar el mando web

1. Recompila y abre ReadyShow (`cargo run` o tu ejecutable actualizado).
2. En el PC abre **Configuración → Control remoto → Activar control**.
3. Conecta el teléfono y el PC a la misma red y abre la dirección que muestra ReadyShow, por ejemplo `http://192.168.1.20:8091`.
4. Pega el código de sesión y pulsa **Conectar con ReadyShow**.
5. Navega por Favoritos, Cantos, Biblias, Imágenes o Videos. Abrir tarjetas no proyecta: pulsa **Proyectar**.
6. La tarjeta que coincide con el texto/referencia visible se marca en rojo **EN VIVO**. No se muestra el antiguo cuadro superior de contenido proyectado.
7. El estado, la biblioteca y las tarjetas se actualizan cada dos segundos mientras la PWA está visible. No hace falta recargar.
8. Usa los botones inferiores para mostrar/ocultar la pantalla, pausar/reanudar y silenciar video. Sin segundo monitor se abre la ventana del proyector en el monitor del PC.
9. **Desconectar PC** termina la sesión del navegador; desactivar el control en el PC revoca el acceso de todos.

El mando requiere el PC encendido. No guarda ni reintenta órdenes para ejecutarlas después. El código de sesión queda en `sessionStorage`; nunca se guarda en IndexedDB ni en copias. Se conserva el protocolo `/api`, POST JSON, bearer token y protección de origen del servidor Rust. El puerto es 8091, independiente de OBS (8090).

## Migrar los datos anteriores a la aplicación Kotlin

**No se borra IndexedDB ni ningún dato anterior del navegador.**

1. Abre la PWA desde la **misma dirección y navegador** donde guardaste los datos. HTTP, HTTPS y puertos distintos tienen bases separadas.
2. Si existen registros anteriores, aparece **Migrar datos anteriores a Android**.
3. Despliega esa opción y pulsa **Exportar datos anteriores con archivos**. La copia mantiene el formato `readyshow-local`, versión 1, y los seis grupos de datos. Límite de copia: 150 MB.
4. Instala y abre el APK del proyecto `readyshow-android`.
5. En Android entra en **Ajustes → Importar copia de PWA / Android**, elige el JSON y confirma. Esto reemplaza los datos locales de la app nativa; no cambia el PC ni elimina el original del navegador.

La implementación offline anterior también se conserva como referencia de migración en `readyshow-android/migration/pwa-offline-reference`. Los módulos locales que siguen en esta carpeta se mantienen como referencia y para probar el formato de migración; la entrada `app.js` solo inicia mando remoto, instalación y exportación de datos anteriores.

## Instalación opcional de la PWA

Puedes usar HTTP local para el mando web, sin instalación. Instalar esta PWA y guardar su interfaz con Service Worker requiere **HTTPS confiable** en Android. La app Kotlin se instala por APK y **no requiere HTTPS ni Caddy** para usar el servidor HTTP del PC.

Para instalar el mando web:

1. Instala Caddy en el PC, cambia la IP en `Caddyfile.example` y ejecuta desde la raíz:

   ```sh
   caddy run --config remote-pwa/Caddyfile.example --adapter caddyfile
   ```

2. Instala en Android **solo el certificado público** `root.crt` de la autoridad local de Caddy como CA de confianza. Está en el directorio de datos de Caddy, `pki/authorities/local/root.crt`; puedes consultar `caddy.AppDataDir` con `caddy environ` bajo el mismo usuario. No copies `root.key`.
3. Abre `https://IP-del-PC:8443` en Chrome, sin advertencia de certificado, y usa **Instalar aplicación**.
4. Conserva el mismo origen para volver a conectar al PC y acceder a datos anteriores. El proxy mantiene `/api` en el mismo origen y no abre CORS.

La interfaz puede abrir desde caché con el PC apagado, pero controlar la proyección requiere la conexión al PC. El Service Worker no almacena API, códigos, miniaturas ni órdenes. Las actualizaciones se aplican al cerrar todas las ventanas; **Buscar actualización del mando** consulta una nueva versión con el PC disponible.

No se necesitan cuentas, backend cloud, Internet durante el uso ni puertos abiertos en el router. Permite 8091 (o 8443 para Caddy) solo en tu red privada si el firewall lo requiere.

## Código y pruebas

- `app.js`: arranque de mando, PWA y migración.
- `modules/remote.js`: protocolo existente, biblioteca, miniaturas, controles y sincronización.
- `modules/projection.js`: marcado rojo a partir de la salida real.
- `modules/migration.js` y `modules/storage.js`: exportación de IndexedDB anterior, sin eliminarlo.
- `modules/pwa.js`, `sw.js`: instalación opcional y caché de la interfaz.
- `modules/local.js`: referencia de la interfaz anterior, no se carga desde la PWA actual.
- `src/remote_control.rs`: entrega de recursos estáticos y API Rust.

```sh
cargo test
cd remote-pwa
npm ci
npm test
npx playwright install chromium
npm run test:browser
```

Las pruebas de navegador comprueban acceso remoto, órdenes reales contra un servidor local de prueba con el contrato Rust, sincronización, rojo EN VIVO, diseño a 320/390/768/1366 px y exportación de datos anteriores con archivos sin borrarlos. Las pruebas Rust comprueban el servidor y autenticación. Las pruebas de Android se ejecutan desde el proyecto nativo.

Referencias: [contextos seguros para Service Workers](https://developer.mozilla.org/en-US/docs/Web/API/Service_Worker_API/Using_Service_Workers), [HTTPS local de Caddy](https://caddyserver.com/docs/automatic-https#local-https).
