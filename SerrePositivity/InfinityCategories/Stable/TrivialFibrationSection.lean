module
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationSquares

/-! # 自明 Kan fibration の厳密な切断の完全性

概要：厳密な切断も零対象と普遍四角形を保存し反映する。
方針：射影との合成が恒等であることを保存反映の判定に代入する。
規約：切断の選択は任意。使われ方：β3 の安定性の双方向の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
variable {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]


/-- 自明 Kan fibration の厳密な切断は零対象を保ち反映する。 -/
lemma isZeroVertex_iff_map_section_of_trivialKanFibration
    (q : E ⟶ B) [TrivialKanFibration q] (s : B ⟶ E) (hs : s ≫ q = 𝟙 B) (x : B _⦋0⦌) :
    IsZeroVertex x ↔ IsZeroVertex (s.app (Opposite.op ⦋0⦌) x) := by
  have h := isZeroVertex_iff_map_of_trivialKanFibration q (s.app (Opposite.op ⦋0⦌) x)
  have he := ConcreteCategory.congr_hom (congrArg (fun f : B ⟶ B => f.app (Opposite.op ⦋0⦌)) hs) x
  change q.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) x) = x at he
  rw [he] at h
  exact h.symm

/-- 自明 Kan fibration の厳密な切断は引き戻し四角形を保ち反映する。 -/
lemma isPullbackSquare_iff_postcomp_section_of_trivialKanFibration
    (q : E ⟶ B) [TrivialKanFibration q] (s : B ⟶ E) (hs : s ≫ q = 𝟙 B) (F : Δ[1] ⊗ Δ[1] ⟶ B) :
    IsPullbackSquare F ↔ IsPullbackSquare (F ≫ s) := by
  have h := isPullbackSquare_iff_postcomp_trivialKanFibration q (F ≫ s)
  rw [Category.assoc, hs, Category.comp_id] at h
  exact h.symm

/-- 自明 Kan fibration の厳密な切断は押し出し四角形を保ち反映する。 -/
lemma isPushoutSquare_iff_postcomp_section_of_trivialKanFibration
    (q : E ⟶ B) [TrivialKanFibration q] (s : B ⟶ E) (hs : s ≫ q = 𝟙 B) (F : Δ[1] ⊗ Δ[1] ⟶ B) :
    IsPushoutSquare F ↔ IsPushoutSquare (F ≫ s) := by
  have h := isPushoutSquare_iff_postcomp_trivialKanFibration q (F ≫ s)
  rw [Category.assoc, hs, Category.comp_id] at h
  exact h.symm

/-- 自明 Kan fibration の厳密な切断は完全。 -/
lemma isExactFunctor_section_of_trivialKanFibration
    (q : E ⟶ B) [TrivialKanFibration q] (s : B ⟶ E) (hs : s ≫ q = 𝟙 B) : IsExactFunctor s where
  preservesZero x hx := (isZeroVertex_iff_map_section_of_trivialKanFibration q s hs x).1 hx
  preservesCofiber t ht :=
    (isPushoutSquare_iff_postcomp_section_of_trivialKanFibration q s hs t.square).1 ht

end SerrePositivity.InfinityCategories
