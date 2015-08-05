@echo off
set test_dir="..\Tests"
set run="..\Debug\vcc"
echo ====================== BEGIN SORTED ======================
%run% %test_dir%\sorted-sll\sorted_insert.c ^
      %test_dir%\sorted-sll\insertion_sort_copy.c ^
      %test_dir%\sorted-sll\sorted_delete_all.c ^
      %test_dir%\sorted-sll\reverse_sorted.c ^
      %test_dir%\sorted-sll\sorted_find.c ^
      %test_dir%\sorted-sll\merge_sort_copy.c ^
      %test_dir%\sorted-sll\sorted_insert_iter.c ^
      %test_dir%\sorted-sll\find_last_sorted.c ^
      %test_dir%\sorted-sll\concat_sorted.c ^
      %test_dir%\sorted-sll\quick_sort.c ^
      | findstr "sorted_insert insertion_sort_copy sorted_delete_all reverse_sorted sorted_find merge_sort_copy sorted_insert_iter find_last_sorted concat_sorted quick_sort function error"
echo ======================  END SORTED ======================
