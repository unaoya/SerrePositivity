module
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy

/-! # 固定左加群を動かすtensor関手の自然変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def rightTensorLeftMap {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    rightTensorFunctor A D (ForgetEnrichment.to (Complex A) L) ⟶
      rightTensorFunctor A D (ForgetEnrichment.to (Complex A) L') where
  app M := map A D (𝟙 M) g
  naturality {M N} f := by
    change map A D f (𝟙 L) ≫ map A D (𝟙 N) g = map A D (𝟙 M) g ≫ map A D f (𝟙 L')
    rw [← map_comp, ← map_comp]
    simp only [Category.id_comp, Category.comp_id]

lemma rightTensorLeftMap_id (L : LeftModuleCategory A D) :
    rightTensorLeftMap A D (𝟙 L) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  exact map_id A D M L

lemma rightTensorLeftMap_comp {L L' L'' : LeftModuleCategory A D} (f : L ⟶ L') (g : L' ⟶ L'') :
    rightTensorLeftMap A D (f ≫ g) = rightTensorLeftMap A D f ≫ rightTensorLeftMap A D g := by
  apply NatTrans.ext
  funext M
  change map A D (𝟙 M) (f ≫ g) = map A D (𝟙 M) f ≫ map A D (𝟙 M) g
  simpa only [Category.id_comp] using map_comp A D (𝟙 M) (𝟙 M) f g

/-- 全Hom境界による主K(D)上でも左加群の射は自然変換を与える。 -/
def rightTensorHomotopyLeftMap {L L' : LeftModuleCategory A D} (g : L ⟶ L') :
    rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⟶
      rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') :=
  CategoryTheory.Quotient.natTransLift _
    (eqToHom (rightTensorHomotopyFunctor_fac A D (ForgetEnrichment.to (Complex A) L)) ≫
      Functor.whiskerRight (rightTensorLeftMap A D g)
        (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) ≫
      eqToHom (rightTensorHomotopyFunctor_fac A D (ForgetEnrichment.to (Complex A) L')).symm)

lemma rightTensorHomotopyLeftMap_app {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (M : ModuleCategory A D) :
    (rightTensorHomotopyLeftMap A D g).app ((moduleToHomotopy A D).obj M) =
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map (map A D (𝟙 M) g) := by
  simp only [rightTensorHomotopyLeftMap, CategoryTheory.Quotient.natTransLift_app,
    NatTrans.comp_app, eqToHom_app]
  rfl

lemma rightTensorHomotopyLeftMap_id (L : LeftModuleCategory A D) :
    rightTensorHomotopyLeftMap A D (𝟙 L) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (rightTensorHomotopyLeftMap A D (𝟙 L)).app ((moduleToHomotopy A D).obj M) = 𝟙 _
  rw [rightTensorHomotopyLeftMap_app, map_id, CategoryTheory.Functor.map_id]
  rfl

lemma rightTensorHomotopyLeftMap_comp {L L' L'' : LeftModuleCategory A D}
    (f : L ⟶ L') (g : L' ⟶ L'') :
    rightTensorHomotopyLeftMap A D (f ≫ g) =
      rightTensorHomotopyLeftMap A D f ≫ rightTensorHomotopyLeftMap A D g := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (rightTensorHomotopyLeftMap A D (f ≫ g)).app ((moduleToHomotopy A D).obj M) =
    (rightTensorHomotopyLeftMap A D f).app ((moduleToHomotopy A D).obj M) ≫
      (rightTensorHomotopyLeftMap A D g).app ((moduleToHomotopy A D).obj M)
  rw [rightTensorHomotopyLeftMap_app, rightTensorHomotopyLeftMap_app,
    rightTensorHomotopyLeftMap_app, ← CategoryTheory.Functor.map_comp]
  congr 1
  simpa only [Category.id_comp] using map_comp A D (𝟙 M) (𝟙 M) f g

/-- 左加群の閉零圏から、主K(D)上のtensor関手の圏への関手。 -/
def rightTensorHomotopyBifunctor : LeftModuleCategory A D ⥤
    (ModuleHomotopyCategory A D ⥤ _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) where
  obj L := rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L)
  map g := rightTensorHomotopyLeftMap A D g
  map_id L := rightTensorHomotopyLeftMap_id A D L
  map_comp f g := rightTensorHomotopyLeftMap_comp A D f g

end SerrePositivity.DifferentialGraded.BalancedTensor
