module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRowComparison
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# pd de Rham 第 0 行と pd Čech 複体

## 概要
第 0 行の外次数零を消し、余単体的な pd 環の台加群に同一視する。

## 方針
零次外冪の標準同型とテンソル積の右単位律を使う。

## 規約
比較は基底環線形。

## 使われ方
pd de Rham 総複体から pd Čech コホモロジーへの射。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology SerrePositivity.Cosimplicial
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) (k : Type u) [CommRing k] (r : ℕ)

/-- pd Čech 模型の余単体的な台環。 -/
abbrev pdCechRings := pdModel p k r ⋙ Under.forget (CommRingCat.of k)

/-- pd Čech 模型の台環への係数の構造射。 -/
def pdCechBase : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ pdCechRings p k r where
  app n := ((pdModel p k r).obj n).hom
  naturality _ _ f := (Category.id_comp _).trans (Under.w ((pdModel p k r).map f)).symm

private def rowZeroTerm (n : SimplexCategory) :
    (pdTerm p k r n.len ⊗[k] (⋀[k]^0 (CopyModule k r n))) ≃ₗ[k] pdTerm p k r n.len :=
  (TensorProduct.congr (LinearEquiv.refl k _) (exteriorPower.zeroEquiv k _)).trans
    (TensorProduct.rid k _)

private def rowZeroIso : pdRow p k r 0 ≅ pdCoefficients p k r :=
  NatIso.ofComponents (fun n => (rowZeroTerm p k r n).toModuleIso) (fun {m n} θ => by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f w
    change pdTerm p k r m.len at f
    change ⋀[k]^0 (CopyModule k r m) at w
    let Eₘ := exteriorPower.zeroEquiv k (CopyModule k r m)
    let Eₙ := exteriorPower.zeroEquiv k (CopyModule k r n)
    change Eₙ (exteriorPower.map 0 (copyModuleMap k r θ) w) • pdTermMap p k r θ f =
      pdTermMap p k r θ (Eₘ w • f)
    rw [map_smul]
    have h := DFunLike.congr_fun (exteriorPower.zeroEquiv_naturality (copyModuleMap k r θ)) w
    exact congrArg (fun z : k => z • pdTermMap p k r θ f) h)

private def coeffIso : pdCoefficients p k r ≅ toModules k (pdCechRings p k r) (pdCechBase p k r) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {m n} θ => by
    change (pdCoefficients p k r).map θ ≫ 𝟙 _ =
      𝟙 _ ≫ (toModules k (pdCechRings p k r) (pdCechBase p k r)).map θ
    rw [Category.comp_id, Category.id_comp]
    rfl)

/-- 第 0 行は pd Čech 環の台加群の交代余面複体。 -/
def pdDeRhamRowZeroIso :
    (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (pdRow p k r 0) ≅
      (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k (pdCechRings p k r) (pdCechBase p k r)) :=
  (alternatingCofaceMapComplex (ModuleCat.{u} k)).mapIso (rowZeroIso p k r ≪≫ coeffIso p k r)

/-- 総複体から第 0 行への射影による pd Čech コホモロジー同型。 -/
def pdDeRhamTotalToCech (i : ℕ) :
    (pdDeRhamTotal p k r).homology i ≃+ cohomology (pdCechRings p k r) i := by
  let := pdDeRhamRowZeroProjection_quasiIso p k r
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) i
  let e := (asIso (HomologicalComplex.homologyMap (pdDeRhamRowZeroProjection p k r) i)) ≪≫
    F.mapIso (pdDeRhamRowZeroIso p k r)
  exact e.toLinearEquiv.toAddEquiv.trans
    (cohomologyEquivModuleHomology k (pdCechRings p k r) (pdCechBase p k r) i).symm

end SerrePositivity.BhattScholze.Prismatic
