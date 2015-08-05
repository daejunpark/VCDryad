@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN GLIST ======================
%r% %test_dir%\glist\g_list_free.c ^
    %test_dir%\glist\g_list_find.c ^
    %test_dir%\glist\g_list_last.c ^
    %test_dir%\glist\g_list_index.c ^
    %test_dir%\glist\g_list_length.c ^
    %test_dir%\glist\g_list_nth.c ^
    %test_dir%\glist\g_list_nth_data.c ^
    %test_dir%\glist\g_list_position.c ^
    %test_dir%\glist\g_list_prepend.c ^
    %test_dir%\glist\g_list_reverse.c ^
    | findstr "g_list error"
echo ======================  END GLIST ======================
