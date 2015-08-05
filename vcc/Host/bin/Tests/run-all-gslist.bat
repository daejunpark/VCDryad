@echo off
set test_dir="..\Tests"
set run="..\Debug\vcc"
echo ====================== BEGIN GSLIST ======================
%run% %test_dir%\gslist\g_slist_prepend.c ^
      %test_dir%\gslist\g_slist_last.c ^
      %test_dir%\gslist\g_slist_concat.c ^
      %test_dir%\gslist\g_slist_append.c ^
      %test_dir%\gslist\g_slist_insert.c ^
      %test_dir%\gslist\g_slist_insert_before.c ^
      %test_dir%\gslist\g_slist_remove.c ^
      %test_dir%\gslist\g_slist_remove_all.c ^
      %test_dir%\gslist\g_slist_remove_link.c ^
      %test_dir%\gslist\g_slist_delete_link.c ^
      %test_dir%\gslist\g_slist_free.c ^
      %test_dir%\gslist\g_slist_copy.c ^
      %test_dir%\gslist\g_slist_reverse.c ^
      %test_dir%\gslist\g_slist_nth.c ^
      %test_dir%\gslist\g_slist_nth_data.c ^
      %test_dir%\gslist\g_slist_find.c ^
      %test_dir%\gslist\g_slist_position.c ^
      %test_dir%\gslist\g_slist_index.c ^
      %test_dir%\gslist\g_slist_length.c ^
      %test_dir%\gslist\g_slist_insert_sorted.c ^
      %test_dir%\gslist\g_slist_sort_merge.c ^
      %test_dir%\gslist\g_slist_sort_real.c ^
      | findstr "slist function error"
echo ======================  END GSLIST  ======================
