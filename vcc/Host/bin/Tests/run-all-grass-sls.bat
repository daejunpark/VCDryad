@echo off
set test_dir="..\Tests"
set r="..\Debug\vcc"
echo ====================== BEGIN SLS ======================
%r% %test_dir%\grass\sls_concat.c ^
    %test_dir%\grass\sls_copy.c ^
    %test_dir%\grass\sls_dispose.c ^
    %test_dir%\grass\sls_filter.c ^
    %test_dir%\grass\sls_insert.c ^
    %test_dir%\grass\sls_remove.c ^
    %test_dir%\grass\sls_reverse.c ^
    %test_dir%\grass\sls_traverse.c ^
    %test_dir%\grass\sls_double_all.c ^
    %test_dir%\grass\sls_pairwise_sum.c ^
    %test_dir%\grass\sls_insertion_sort.c ^
    %test_dir%\grass\sls_split.c ^
    %test_dir%\grass\sls_merge.c ^
    %test_dir%\grass\sls_merge_sort.c ^
    | findstr "Verification function error"
echo ======================  END SLS ======================
