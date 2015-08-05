@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN DL ======================
%r% %test_dir%\grass\dl_concat.c ^
    %test_dir%\grass\dl_copy.c ^
    %test_dir%\grass\dl_dispose.c ^
    %test_dir%\grass\dl_filter.c ^
    %test_dir%\grass\dl_insert.c ^
    %test_dir%\grass\dl_remove.c ^
    %test_dir%\grass\dl_reverse.c ^
    %test_dir%\grass\dl_traverse.c ^
    | findstr "Verification function error"
echo ======================  END DL ======================
