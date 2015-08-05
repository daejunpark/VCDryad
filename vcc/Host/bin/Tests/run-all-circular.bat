@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN CIRCULAR ======================
%r% %test_dir%\circular-list\circular-list-insert-front.c ^
    %test_dir%\circular-list\circular-list-insert-back.c ^
    %test_dir%\circular-list\circular-list-delete-front.c ^
    %test_dir%\circular-list\circular-list-delete-back.c ^
    | findstr "circular lseg_delete error"
echo ======================  END CIRCULAR ======================
