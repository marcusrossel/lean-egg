import Egg

-- This case shows up in the proof of `List.zip_map'` in Batteries.

/-- error: egg does not support using auxiliary declarations -/
#guard_msgs in
theorem t : a = b := by
  egg [t]
