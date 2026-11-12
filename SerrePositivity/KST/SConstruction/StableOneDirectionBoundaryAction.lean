module
public import SerrePositivity.KST.SConstruction.StableOneDirectionRealization
public import SerrePositivity.KST.SConstruction.OneDirectionBoundary
public import SerrePositivity.KST.SConstruction.CofiberFamilyActionLaws

/-!
概要：一次方向実現の全自然同値族が、元の全零境界を保存することを示す。
方針：元の零次数への制限の豊穣自然性から、各像の原像を保持する。
規約：入力の高次パラメータを固定する。使われ方：隣接段比較の同じ商への降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants

/-- 概要：各零方向の像は全自然同値族の作用で保存される。
方針：元の零方向からの包含を全多次数図式の自然性で移す。
規約：同じ原像を使う。使われ方：全零境界への制限。 -/
lemma stableOneDirectionAction_mem_zeroRange (r : ℕ) (j : Fin r)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C)).obj n)
    (p : (C ⟶[SSet.{u}] D).obj n)
    (hx : x ∈ (oneDirectionZeroRange r j (stableCategoryModel C)).obj n) :
    (stableOneDirectionAction r C D).app n (x, p) ∈
      (oneDirectionZeroRange r j (stableCategoryModel D)).obj n := by
  obtain ⟨y, rfl⟩ := hx
  let θ := (oneDirectionIndex r).map ((zeroDirectionsIndexNat {j}).app (fun _ => n))
  let E := stableMultiSCoreEnrichedDiagram.{u} (r + 1)
  have h := congrArg (fun q => q.app n (y, p)) ((E.map θ).property C D)
  refine ⟨(uncurry ((E.obj _).map C D)).app n (y, p), ?_⟩
  exact h.symm.trans (stableOneDirectionAction_app r C D n
    ((oneDirectionZeroInclusion r j (stableCategoryModel C)).app n y) p).symm

/-- 概要：残りの全零方向の合併も全高次入力族で保存される。
方針：元の合併の元を同じ方向に属する元として保つ。
規約：空の合併も含む。使われ方：元の全境界商への降下。 -/
lemma stableOneDirectionAction_mem_fatBoundary (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C)).obj n)
    (p : (C ⟶[SSet.{u}] D).obj n)
    (hx : x ∈ (oneDirectionFatBoundary r (stableCategoryModel C)).obj n) :
    (stableOneDirectionAction r C D).app n (x, p) ∈
      (oneDirectionFatBoundary r (stableCategoryModel D)).obj n := by
  simp only [oneDirectionFatBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, stableOneDirectionAction_mem_zeroRange r j C D n x p hj⟩

/-- 概要：元の全零境界への全パラメータ制限作用。
方針：保存した各単体の像を同じ部分複体へ制限する。
規約：元の境界包含を保持する。使われ方：商作用の崩壊条件。 -/
def stableOneDirectionBoundaryAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (oneDirectionFatBoundary r (stableCategoryModel C) : SSet.{u}) ⊗
      (C ⟶[SSet.{u}] D) ⟶
        (oneDirectionFatBoundary r (stableCategoryModel D) : SSet.{u}) :=
  Subcomplex.lift
    (((oneDirectionFatBoundary r (stableCategoryModel C)).ι ⊗ₘ 𝟙 _) ≫
      stableOneDirectionAction r C D) (by
      intro n y hy
      obtain ⟨p, rfl⟩ := hy
      exact stableOneDirectionAction_mem_fatBoundary r C D n p.1.val p.2 p.1.property)

/-- 概要：境界包含後には同じ元の全作用を回収する。
方針：部分複体への制限の包含式を使う。
規約：全単体の等式。使われ方：同じ商の普遍性。 -/
lemma stableOneDirectionBoundaryAction_inclusion (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    stableOneDirectionBoundaryAction r C D ≫
        (oneDirectionFatBoundary r (stableCategoryModel D)).ι =
      ((oneDirectionFatBoundary r (stableCategoryModel C)).ι ⊗ₘ 𝟙 _) ≫
        stableOneDirectionAction r C D := Subcomplex.lift_ι _ _

end SerrePositivity.KST.SConstruction
