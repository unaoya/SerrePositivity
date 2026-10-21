module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology

/-!
概要：非可換 dg 代数の underlying complex に、正しい向きの smart Postnikov 切断を作る。
方針：τ≥−n の実関手と自然な射影を使い、整数次数 n 以下の同型を保持する。
規約：この複体の切断へ代数の積をまだ供給しない。使われ方：代数切断の underlying 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits HomologicalComplex ComplexShape
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def postnikovComplex (n : ℤ) : Mon (Complex R) ⥤ Complex R :=
  Mon.forget (Complex R) ⋙ (embeddingUpIntGE (-n)).truncGEFunctor (ModuleCat R)

def postnikovProjection (n : ℤ) : Mon.forget (Complex R) ⟶ postnikovComplex R n :=
  Functor.whiskerLeft (Mon.forget (Complex R))
    ((embeddingUpIntGE (-n)).πTruncGENatTrans (ModuleCat R))

lemma postnikovProjection_quasiIsoAt (B : Mon (Complex R)) (n j : ℤ) (hj : j ≤ n) :
    QuasiIsoAt ((postnikovProjection R n).app B) (-j) :=
  CochainComplex.quasiIsoAt_πTruncGE B.X (-n) (-j) (by omega)

lemma postnikovProjection_groups_isIso (B : Mon (Complex R)) (n j : ℤ) (hj : j ≤ n) :
    IsIso ((complexGroups R j).map ((postnikovProjection R n).app B)) := by
  haveI := postnikovProjection_quasiIsoAt R B n j hj
  change IsIso (AddCommGrpCat.toCommGrp.map
    ((forget₂ (ModuleCat R) AddCommGrpCat).map
      (homologyMap ((postnikovProjection R n).app B) (-j))))
  infer_instance

lemma postnikovComplex_homology_zero (B : Mon (Complex R)) (n j : ℤ) (hj : n < j) :
    IsZero (((postnikovComplex R n).obj B).homology (-j)) := by
  change IsZero ((B.X.truncGE (-n)).homology (-j))
  exact CochainComplex.isZero_of_isGE _ (-n) (-j) (by omega)

lemma postnikovComplex_groups_subsingleton (B : Mon (Complex R)) (n j : ℤ) (hj : n < j) :
    Subsingleton ((complexGroups R j).obj ((postnikovComplex R n).obj B)) := by
  haveI := (ModuleCat.isZero_iff_subsingleton).1 (postnikovComplex_homology_zero R B n j hj)
  change Subsingleton (Multiplicative (((postnikovComplex R n).obj B).homology (-j)))
  infer_instance

lemma postnikovComplex_map_quasiIso_iff {B C : Mon (Complex R)} (f : B ⟶ C) (n : ℤ) :
    QuasiIso ((postnikovComplex R n).map f) ↔
      ∀ j : ℤ, j ≤ n → Function.Bijective ((groups R j).map f).hom := by
  change QuasiIso (CochainComplex.truncGEMap f.hom (-n)) ↔ _
  rw [CochainComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h j hj
    exact (groups_map_bijective_iff R f j).2 (h (-j) (by omega))
  · intro h i hi
    have hp := (groups_map_bijective_iff R f (-i)).1 (h (-i) (by omega))
    simpa only [neg_neg] using hp

lemma postnikovComplex_connected (B : Mon (Complex R)) (hB : IsConnective R B)
    (n : ℤ) (hn : 0 ≤ n) : ((postnikovComplex R n).obj B).IsLE 0 := by
  apply (CochainComplex.isLE_iff _ 0).2
  intro i hi
  haveI : B.X.IsLE 0 := hB
  haveI : QuasiIsoAt ((postnikovProjection R n).app B) i :=
    CochainComplex.quasiIsoAt_πTruncGE B.X (-n) i (by omega)
  exact (exactAt_iff_of_quasiIsoAt ((postnikovProjection R n).app B) i).1
    (CochainComplex.exactAt_of_isLE B.X 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
