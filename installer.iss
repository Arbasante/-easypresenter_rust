[Setup]
; Nombre y versión de tu app
AppName=EasyPresenter
AppVersion=1.0.0
DefaultDirName={localappdata}\EasyPresenter
DefaultGroupName=EasyPresenter
UninstallDisplayIcon={app}\easy-presenter-slint.exe
Compression=lzma2
SolidCompression=yes
OutputDir=Output
OutputBaseFilename=Instalar_EasyPresenter_v1.0
; PrivilegesRequired=lowest permite instalar sin ser administrador
PrivilegesRequired=lowest

[Files]
; 1. El ejecutable que compila GitHub en la nube
Source: "target\release\easy-presenter-slint.exe"; DestDir: "{app}"; Flags: ignoreversion

; 2. Tus bases de datos (importante para que el programa no abra vacío)
Source: "data\*"; DestDir: "{app}\data"; Flags: ignoreversion recursesubdirs createallsubdirs

; 3. El motor de video GStreamer (necesario para que funcione el video en Windows)
; Nota: El script de GitHub lo descargará automáticamente
Source: "gstreamer-runtime.msi"; DestDir: "{tmp}"; Flags: deleteafterinstall

[Icons]
Name: "{autodesktop}\EasyPresenter"; Filename: "{app}\easy-presenter-slint.exe"
Name: "{group}\EasyPresenter"; Filename: "{app}\easy-presenter-slint.exe"

[Run]
; Instala GStreamer de forma silenciosa antes de que el usuario abra la app
Filename: "msiexec.exe"; Parameters: "/i ""{tmp}\gstreamer-runtime.msi"" /qn"; StatusMsg: "Instalando componentes de video..."; Flags: waituntilterminated

; Iniciar el programa al terminar
Filename: "{app}\easy-presenter-slint.exe"; Description: "Lanzar EasyPresenter"; Flags: nowait postinstall skipifsilent