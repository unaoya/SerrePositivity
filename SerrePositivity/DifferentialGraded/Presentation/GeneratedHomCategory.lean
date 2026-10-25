module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomComposition
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomUnit
public import SerrePositivity.DifferentialGraded.Category.FaithfulHomConstruction
public import SerrePositivity.DifferentialGraded.Category.Induced
/-!
概要：指定斉次係数の単位・微分・合成閉包を実 dg 圏として構成する。
方針：係数 span の Hom 複体と制限合成から、単射比較で三法則を反映する。
規約：対象ラベルと元の実 Hom への忠実な評価を保持する。
使われ方：c′ の共通出発圏の係数精密化と固定基底コードへの輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {I J : Type u} (source target : I → J) (degree : I → ℤ)
  (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] (value : J → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
namespace DGGeneratedHomWord

lemma homComposition_inclusion (x y z : J) :
    homComposition source target degree R D value coefficient x y z ≫
      inclusion source target degree R D value coefficient x z =
    (inclusion source target degree R D value coefficient x y ⊗ₘ
      inclusion source target degree R D value coefficient y z) ≫
      eComp (Complex R) (value x) (value y) (value z) := by
  apply tensorHom_ext
  intro p q n hn
  simp only [homComposition, HomologicalComplex.comp_f, ι_tensorLift_assoc,
    ι_tensorHom_assoc, Category.assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  rfl

@[instance_reducible] def category : DGCategory R J := by
  letI := inducedDGCategory R value
  exact dgCategoryOfFaithfulHomMaps R J
    (homComplex source target degree R D value coefficient)
    (inclusion source target degree R D value coefficient)
    (homUnit source target degree R D value coefficient)
    (homComposition source target degree R D value coefficient)
    (homUnit_inclusion source target degree R D value coefficient)
    (homComposition_inclusion source target degree R D value coefficient)

def evaluation :
    letI := category source target degree R D value coefficient
    DGFunctor R J D := by
  letI := category source target degree R D value coefficient
  exact
    { obj := value
      map := inclusion source target degree R D value coefficient
      map_id := homUnit_inclusion source target degree R D value coefficient
      map_comp := homComposition_inclusion source target degree R D value coefficient }

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
