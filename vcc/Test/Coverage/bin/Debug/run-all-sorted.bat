echo off
echo ====================== BEGIN SORTED ======================
vcc /smoke sorted_insert.c ^
    insertion_sort_copy.c ^
    sorted_delete_all.c ^
    reverse_sorted.c ^
    sorted_find.c ^
    merge_sort_copy.c ^
    sorted_insert_iter.c ^
    find_last_sorted.c ^
    concat_sorted.c ^
    quick_sort.c ^
    | grep sort
::    /pipe:dump+after+dryad-end > sll_dump_after_dryad_end
echo ======================  END SORTED ======================
