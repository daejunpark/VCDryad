@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN REC ======================
%r% %test_dir%\grass\rec_concat.c ^
    %test_dir%\grass\rec_copy.c ^
    %test_dir%\grass\rec_dispose.c ^
    %test_dir%\grass\rec_filter.c ^
    %test_dir%\grass\rec_insert.c ^
    %test_dir%\grass\rec_remove.c ^
    %test_dir%\grass\rec_reverse.c ^
    %test_dir%\grass\rec_traverse.c ^
    | findstr "Verification function error"
echo ======================  END REC ======================
