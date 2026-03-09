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

; 3. Las DLLs base de GStreamer (copiadas por el YAML a target\release)
Source: "target\release\*.dll"; DestDir: "{app}"; Flags: ignoreversion

; 4. Los plugins de video/audio de GStreamer (copiados por el YAML)
Source: "target\release\lib\*"; DestDir: "{app}\lib"; Flags: ignoreversion recursesubdirs createallsubdirs

[Icons]
Name: "{autodesktop}\EasyPresenter"; Filename: "{app}\easy-presenter-slint.exe"
Name: "{group}\EasyPresenter"; Filename: "{app}\easy-presenter-slint.exe"

[Run]
; Iniciar el programa al terminar (Ya no necesitamos instalar el MSI de GStreamer)
Filename: "{app}\easy-presenter-slint.exe"; Description: "Lanzar EasyPresenter"; Flags: nowait postinstall skipifsilent