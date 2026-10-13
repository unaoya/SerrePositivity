module

public import SerrePositivity.CategoryTheory.FiniteBijectionSum

/-! # 固定した有限集合を右に加える関手 -/

@[expose] public section

namespace SerrePositivity.FiniteBijection

open CategoryTheory

/-- n元の標準有限集合を右ブロックとして加える関手。 -/
def addRight (n : ℕ) : FiniteBijection ⥤ FiniteBijection where
  obj a := sumObj a (of n)
  map k := sumMap k (𝟙 (of n))
  map_id a := sumMap_id a (of n)
  map_comp k l := by rw [sumMap_comp, Category.id_comp]

end SerrePositivity.FiniteBijection
