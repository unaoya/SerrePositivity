module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
public import Mathlib.Algebra.Homology.QuasiIso
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology

/-!
# 余単体的代数の射と線形な交代余面複体

## 概要
固定した基底と両立する環の余単体射を、既存の台加群の射に移す。

## 方針
係数の可換図式で線形性を示し、台加法群への忘却で擬同型を判定する。

## 規約
環のコホモロジーには既存の交代余面複体を使う。

## 使われ方
BS 著者版 Theorem 6.4 の厳密な結晶の橋を基底線形な複体へ移す。
-/

public noncomputable section

open CategoryTheory HomologicalComplex AlgebraicTopology

universe u

namespace SerrePositivity.Cosimplicial

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [CommRing k]
variable {X Y : CosimplicialObject CommRingCat.{u}}
variable (ιX : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X)
variable (ιY : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ Y)
variable (f : X ⟶ Y) (hι : ιX ≫ f = ιY)

/-- 基底と両立する環の余単体射を、既存の台加群の射に移す。 -/
def toModulesMap : toModules k X ιX ⟶ toModules k Y ιY where
  app n := by
    letI : Module k (X.obj n) := (ιX.app n).hom.toAlgebra.toModule
    letI : Module k (Y.obj n) := (ιY.app n).hom.toAlgebra.toModule
    exact ModuleCat.ofHom {
      toFun := (f.app n).hom
      map_add' := (f.app n).hom.map_add
      map_smul' := fun r x => by
        change (f.app n).hom ((ιX.app n).hom r * x) =
          (ιY.app n).hom r * (f.app n).hom x
        rw [map_mul]
        exact congrArg (fun a => a * (f.app n).hom x)
          (ConcreteCategory.congr_hom (NatTrans.congr_app hι n) r) }
  naturality {m n} θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (f.naturality θ) x

/-- 基底を保つ余単体射が誘導する、線形な交代余面複体の射。 -/
def moduleCochainMap :
    (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k X ιX) ⟶
      (alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k Y ιY) :=
  (alternatingCofaceMapComplex (ModuleCat.{u} k)).map (toModulesMap k ιX ιY f hι)

private def forgetModuleCochainIso :
    (alternatingCofaceMapComplex AddCommGrpCat).obj
        (X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ≅
      ((forget₂ (ModuleCat.{u} k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        ((alternatingCofaceMapComplex (ModuleCat.{u} k)).obj (toModules k X ιX)) := by
  let F := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let K := (alternatingCofaceMapComplex _).obj (toModules k X ιX)
  let L := (alternatingCofaceMapComplex _).obj
    (X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro a b hab
  have hb : b = a + 1 := hab.symm
  subst b
  change (𝟙 (L.X a)) ≫ (_ : L.X a ⟶ L.X (a + 1)) =
    L.d a (a + 1) ≫ 𝟙 (L.X (a + 1))
  erw [Category.id_comp, Category.comp_id]
  change F.map (K.d a (a + 1)) = L.d a (a + 1)
  dsimp only [K, L, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    CochainComplex.of]
  rw [CochainComplex.of_d, CochainComplex.of_d]
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
  rfl

/-- 環のコホモロジー同型は、基底線形な交代余面複体の擬同型を誘導する。 -/
theorem moduleCochainMap_quasiIso_of_isCohomologyIso (hf : IsCohomologyIso f) :
    QuasiIso (moduleCochainMap k ιX ιY f hι) := by
  let V := forget₂ (ModuleCat.{u} k) AddCommGrpCat
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let g := (alternatingCofaceMapComplex AddCommGrpCat).map (Functor.whiskerRight f U)
  have hg : QuasiIso g := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
    exact hf i
  let eX := forgetModuleCochainIso k ιX
  let eY := forgetModuleCochainIso k ιY
  have hn : g ≫ eY.hom = eX.hom ≫
      (V.mapHomologicalComplex (.up ℕ)).map (moduleCochainMap k ιX ιY f hι) := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rfl
  apply (quasiIso_map_iff_of_preservesHomology (moduleCochainMap k ιX ιY f hι) V).mp
  have : QuasiIso (eX.hom ≫
      (V.mapHomologicalComplex (.up ℕ)).map (moduleCochainMap k ιX ιY f hι)) := by
    rw [← hn]
    infer_instance
  exact quasiIso_of_comp_left eX.hom _

end SerrePositivity.Cosimplicial
