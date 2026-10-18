module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomSection

/-!
# 最大頂点による豊穣関手の立方体評価

概要：F1 の豊穣関手の実際の Hom の評価を、最大頂点の射による標準 Hom の評価へ移す。
方針：端点の等式による Hom の移送を HEq で追跡し、F1 の Hom の計算を使う。
規約：端点の型の移送を新しい整合性の仮定として要求しない。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の二つの比較射の合成の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：豊穣 Hom の端点の等式による移送は立方体評価の異種等号を与える。
方針：二端点の等式を消去して恒等射との合成に戻す。
規約：対象は閉零射の圏の対象として指定する。
使われ方：Kerodon 2.5.9 の F1 の Hom の正規化と比較成分の接続。 -/
lemma cubeEvaluation_object_transport {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    {x y x' y' : ClosedCategory R D} (hx : x = x') (hy : y = y')
    (φ : Coherent.cube T ⟶ SimplicialCategory.sHom x y) :
    HEq (cubeEvaluation (R := R) (D := D) e φ)
      (cubeEvaluation (R := R) (D := D) e
        (φ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hy))) := by
  subst x' y'
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：最大頂点から作った豊穣関手の立方体評価は最大頂点の射での評価に一致する。
方針：F1 の Hom の計算を内部立方体に制限し、端点の等式を立方体評価へ移す。
規約：任意の内部座標集合と任意の番号付けで成り立つ。
使われ方：HA 1.3.1.17 の実際の pinched Hom の比較成分の計算。 -/
lemma coherentHomComparison_cubeEvaluation_heq {x y : ClosedCategory R D} {n : ℕ}
    (σ : StandardSimplex R (D := D) x y n) (i : Fin (n + 1))
    (S : Finset (Set.Ioo (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))) {m : ℕ} (e : Fin m ≃ S) :
    HEq (cubeEvaluation e
      (coherentCubeHom (coherentHomComparisonSimplex (X := x) (Y := y) σ)
        (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
          ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S))
      (cubeEvaluation e
        (pathCubeMap (show (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
          ULift.up (Fin.last (n + 1)) from Fin.castSucc_lt_last i) S ≫
            pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ)) := by
  let hab : (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) <
    ULift.up (Fin.last (n + 1)) := Fin.castSucc_lt_last i
  let φ := coherentCubeHom (R := R) (D := D)
    (coherentHomComparisonSimplex (X := x) (Y := y) σ) hab S
  let hx := coherentHomComparisonObj_cast x y i
  let hy := coherentHomComparisonObj_last x y n
  have hφ : φ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hy) =
      pathCubeMap hab S ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ := by
    change (pathCubeMap hab S ≫ coherentHomComparisonHom σ i.castSucc (Fin.last (n + 1))) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hx hy) = _
    rw [Category.assoc, coherentHomComparisonHom_cast_last (X := x) (Y := y) σ i]
  exact (cubeEvaluation_object_transport e hx hy φ).trans
    (heq_of_eq (congrArg (cubeEvaluation (R := R) (D := D) e) hφ))

end SerrePositivity.InfinityCategories.DoldKanComparison
