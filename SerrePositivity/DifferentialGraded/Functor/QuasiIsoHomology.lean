module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyNaturality
public import SerrePositivity.DifferentialGraded.Complexes.UnitTensor

/-! # Hom準同型からH⁰関手の完全忠実性へ

## 概要
Hom準同型からH⁰関手の完全忠実性へ。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] (F : DGFunctor A D E)

lemma closedHomEquiv_map {x y : ClosedCategory A D} (f : x ⟶ y) :
    closedHomEquiv A E (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) =
      complexMapZeroCycle A (F.map x y) (closedHomEquiv A D x y f) := by
  apply Subtype.ext
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫ F.map x y)).val = _
  rw [cycleFromUnit_postcomp]
  rfl

lemma homotopyHomologyEquiv_map_naturality {x y : ClosedCategory A D}
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y) (F.onHomotopy.map f) =
      homologyMap (F.map x y) 0 (homotopyHomologyEquiv A D x y f) := by
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective f
  change homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
    ((toHomotopy A E).map (F.onClosed.map g)) = _
  rw [homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, closedHomEquiv_map]
  rfl

lemma onHomotopy_map_bijective_of_homQuasiIso (hF : HomQuasiIso F)
    (x y : ClosedCategory A D) :
    Function.Bijective (fun f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y =>
      F.onHomotopy.map f) := by
  let : QuasiIso (F.map x y) := hF x y
  let e := homotopyHomologyEquiv A D x y
  let e' := homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
  let b := (asIso (homologyMap (F.map x y) 0)).toLinearEquiv.toEquiv
  let k := (e.trans b).trans e'.symm
  have hk : (fun f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y =>
      F.onHomotopy.map f) = k := by
    funext f
    apply e'.injective
    change homotopyHomologyEquiv A E (F.onClosed.obj x) (F.onClosed.obj y)
      (F.onHomotopy.map f) = e' (e'.symm (b (e f)))
    rw [e'.apply_symm_apply]
    exact F.homotopyHomologyEquiv_map_naturality f
  rw [hk]
  exact k.bijective

lemma onHomotopy_full_of_homQuasiIso (hF : HomQuasiIso F) : F.onHomotopy.Full where
  map_surjective {x y} := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    exact (F.onHomotopy_map_bijective_of_homQuasiIso hF x y).2

lemma onHomotopy_faithful_of_homQuasiIso (hF : HomQuasiIso F) : F.onHomotopy.Faithful where
  map_injective {x y} := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    exact (F.onHomotopy_map_bijective_of_homQuasiIso hF x y).1

end SerrePositivity.DifferentialGraded.DGFunctor
