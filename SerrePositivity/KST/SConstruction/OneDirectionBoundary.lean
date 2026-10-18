module
public import SerrePositivity.KST.SConstruction.MultiAssemblyBoundary

/-! # 一次方向を固定した実現の残りの零方向
概要：残りの各零方向の像を定義し、その cylinder の組み立ては標的の零境界へ入る。
方針：零方向の自己射と組み立ての添字の可換式を使い、像の固定点を比較する。
規約：外側の次数は 1 のまま。使われ方：reduced suspension への降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：残りの零方向の自己射と組み立ては可換。
方針：先頭は恒等、後続方向は同じ座標の零自己射となる。
規約：標的では方向を succ でずらす。使われ方：零境界 cylinder の像の計算。 -/
lemma oneDirectionAssemblyIndex_zero_commute (r : ℕ) (j : Fin r)
    (d : SimplexCategoryᵒᵖ) (α : d.unop ⟶ ⦋1⦌) :
    (oneDirectionIndex r).map (zeroDirectionsIndexEndomorphism {j} (fun _ => d)) ≫
        oneDirectionAssemblyIndex r d α =
      oneDirectionAssemblyIndex r d α ≫
        zeroDirectionsIndexEndomorphism {j.succ} (fun _ => d) := by
  funext k
  refine Fin.cases ?_ (fun l => ?_) k
  · have hz : zeroDirectionsIndexEndomorphism {j.succ} (fun _ => d)
        (0 : Fin (r + 1)) = 𝟙 d := by
      change zeroCoordinateEndomorphism (0 : Fin (r + 1))
        (decide ((0 : Fin (r + 1)) ∈ ({j.succ} : Finset (Fin (r + 1))))) (fun _ => d) = 𝟙 d
      have hb : decide ((0 : Fin (r + 1)) ∈ ({j.succ} : Finset (Fin (r + 1)))) = false := by
        simp only [Finset.mem_singleton, decide_eq_false_iff_not]
        exact fun h => Fin.succ_ne_zero j h.symm
      rw [hb]
      rfl
    change 𝟙 (Opposite.op ⦋1⦌) ≫ α.op = α.op ≫
      zeroDirectionsIndexEndomorphism {j.succ} (fun _ => d) (0 : Fin (r + 1))
    rw [hz, Category.id_comp, Category.comp_id]
  · change zeroCoordinateEndomorphism l (decide (l ∈ ({j} : Finset (Fin r))))
      (fun _ => d) ≫ 𝟙 d = 𝟙 d ≫
      zeroCoordinateEndomorphism l.succ (decide (l.succ ∈ ({j.succ} : Finset (Fin (r + 1)))))
        (fun _ => d)
    simp only [Category.comp_id, Category.id_comp]
    have hb : decide (l.succ ∈ ({j.succ} : Finset (Fin (r + 1)))) =
        decide (l ∈ ({j} : Finset (Fin r))) := by simp
    rw [hb]
    cases decide (l ∈ ({j} : Finset (Fin r))) <;> rfl

/-- 概要：一次方向を固定した実現で、残りの一方向を零に固定する図式。
方針：残りの対角の前に零固定の添字関手を挿入する。
規約：外側の次数は変えない。使われ方：残りの零境界の包含。 -/
def oneDirectionZeroDiagram (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  multiIndexDiagonal r ⋙ zeroDirectionsIndex {j} ⋙ oneDirectionIndex r ⋙
    multiCoreSConstruction (r + 1) X

/-- 概要：残りの零方向を固定した実現から元の一次方向の実現への射。
方針：添字の零段の自然な包含を対角で写す。
規約：全高次単体を保持する。使われ方：零境界の像の定義。 -/
def oneDirectionZeroInclusion (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (oneDirectionZeroDiagram r j X) ⟶
      (oneDirectionRealizationFunctor r).obj X :=
  simplicialDiagonalFunctor.map (Functor.whiskerLeft (multiIndexDiagonal r)
    (Functor.whiskerRight (zeroDirectionsIndexNat {j})
      (oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X)))

/-- 概要：残りの一方向が零である部分の像。
方針：零段からの写像の range を取る。
規約：部分複体として定義する。使われ方：源の全零境界。 -/
def oneDirectionZeroRange (r : ℕ) (j : Fin r) (X : StableModel.{u}) :
    ((oneDirectionRealizationFunctor r).obj X).Subcomplex :=
  Subcomplex.range (oneDirectionZeroInclusion r j X)

/-- 概要：残りの零方向の像の元はその零自己射で固定される。
方針：零段の包含と次数ごとのレトラクションの分裂を写す。
規約：単体次数は任意。使われ方：組み立ての零境界への所属。 -/
lemma oneDirectionZeroRange_fixed (r : ℕ) (j : Fin r) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionZeroRange r j X).obj d) :
    ((multiCoreSConstruction (r + 1) X).map
      ((oneDirectionIndex r).map (zeroDirectionsIndexEndomorphism {j} (fun _ => d)))).app d x = x := by
  obtain ⟨y, rfl⟩ := hx
  let F := oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X
  change ((F.map ((zeroDirectionsIndexNat {j}).app (fun _ => d)) ≫
    F.map (zeroDirectionsIndexEndomorphism {j} (fun _ => d))).app d) y =
      (F.map ((zeroDirectionsIndexNat {j}).app (fun _ => d))).app d y
  rw [← F.map_comp, zeroDirectionsIndexEndomorphism, ← Category.assoc,
    zeroDirectionsIndexNat_retraction, Category.id_comp]
  rfl

/-- 概要：残りの零方向の像の cylinder は標的の対応する零方向へ入る。
方針：固定点の式を組み立ての添字の可換式で標的へ移す。
規約：区間パラメーターは任意。使われ方：全 cylinder を潰す条件。 -/
lemma multiDiagonalAssembly_zeroRange_mem (r : ℕ) (j : Fin r) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (a : (Δ[1] : SSet.{u}).obj d)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionZeroRange r j X).obj d) :
    (multiDiagonalAssembly r X).app d (a, x) ∈ (zeroDirectionsRange {j.succ} X).obj d := by
  apply (mem_zeroDirectionsRange_iff _ X d _).2
  rw [zeroDirectionsOperator_eq_map]
  change (((multiCoreSConstruction (r + 1) X).map
    (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv a)) ≫
      (multiCoreSConstruction (r + 1) X).map
        (zeroDirectionsIndexEndomorphism {j.succ} (fun _ => d))).app d) x = _
  rw [← CategoryTheory.Functor.map_comp, ← oneDirectionAssemblyIndex_zero_commute,
    CategoryTheory.Functor.map_comp]
  change ((multiCoreSConstruction (r + 1) X).map
    (oneDirectionAssemblyIndex r d (stdSimplex.objEquiv a))).app d
      (((multiCoreSConstruction (r + 1) X).map
        ((oneDirectionIndex r).map (zeroDirectionsIndexEndomorphism {j} (fun _ => d)))).app d x) = _
  rw [oneDirectionZeroRange_fixed r j X d x hx]
  rfl

/-- 概要：一次方向の実現の残りの全零方向の像の合併。
方針：各方向の range の上限を取る。
規約：r=0 では空部分複体。使われ方：源の正準的な点化。 -/
def oneDirectionFatBoundary (r : ℕ) (X : StableModel.{u}) :
    ((oneDirectionRealizationFunctor r).obj X).Subcomplex :=
  ⨆ j : Fin r, oneDirectionZeroRange r j X

/-- 概要：残りの全零境界の cylinder の像は標的の全零境界に属する。
方針：各方向の所属を有限合併へ移す。
規約：全区間パラメーターに適用。使われ方：reduced suspension への降下条件。 -/
lemma multiDiagonalAssembly_fatBoundary_mem (r : ℕ) (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) (a : (Δ[1] : SSet.{u}).obj d)
    (x : ((oneDirectionRealizationFunctor r).obj X).obj d)
    (hx : x ∈ (oneDirectionFatBoundary r X).obj d) :
    (multiDiagonalAssembly r X).app d (a, x) ∈ (zeroDirectionsFatBoundary (r + 1) X).obj d := by
  simp only [oneDirectionFatBoundary, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  have hle : zeroDirectionsRange {j.succ} X ≤ zeroDirectionsFatBoundary (r + 1) X :=
    Finset.le_sup (f := fun k => zeroDirectionsRange (insert k ∅) X) (Finset.mem_univ j.succ)
  exact hle _ (multiDiagonalAssembly_zeroRange_mem r j X d a x hj)

end SerrePositivity.KST.SConstruction
