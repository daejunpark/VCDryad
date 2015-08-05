@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN SV-COMP ======================
%r% %test_dir%\sv-comp\dll_of_dll.c ^
    %test_dir%\sv-comp\rule_60_list_add.c ^
    %test_dir%\sv-comp\rule_60_list_del.c ^
    %test_dir%\sv-comp\rule_60_list_head_add.c ^
    %test_dir%\sv-comp\rule_60_list_head_init.c ^
    | findstr "Verification function error"
echo ======================  END SV-COMP ======================
