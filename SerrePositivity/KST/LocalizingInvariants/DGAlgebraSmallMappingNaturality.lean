module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSmallMappingEquiv
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeFrame

/-!
概要：小さい単体集合の実乗法的写像比較の自然性と指定底の照合。
方針：実 AW 関手・元の標的射・余単位の全自然性を用いる。
規約：通常の全単体比較のまま、元の射と固定底を保持する。
使われ方：実ホーンの制限と指定底に相対的な充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

def simplicialConvolutionTargetNatTrans {B C : Mon (Complex R)} (q : B ⟶ C) :
    simplicialConvolution R B ⟶ simplicialConvolution R C :=
  Functor.whiskerLeft (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor R).op
    (convolutionTargetNatTrans R q)

def simplicialConvolutionConstant (B : Mon (Complex R)) :
    (Functor.const SSet.{0}ᵒᵖ).obj B ⟶ simplicialConvolution R B :=
  Functor.whiskerLeft (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor R).op
    (convolutionConstantNatTrans R B)

lemma smallMultiplicativeMappingCurry_precompose {A B : Mon (Complex R)} {K L : SSet.{0}}
    (f : A ⟶ (simplicialConvolution R B).obj (op L)) (g : K ⟶ L) :
    SSet.uliftFunctor.{u, 0}.map g ≫ smallMultiplicativeMappingCurry R f =
      smallMultiplicativeMappingCurry R (f ≫ (simplicialConvolution R B).map g.op) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change ULift.{u, 0} (K.obj n) at z
  change f ≫ (simplicialConvolution R B).map
      (SSet.yonedaEquiv.{0}.symm (g.app n z.down)).op =
    (f ≫ (simplicialConvolution R B).map g.op) ≫
      (simplicialConvolution R B).map (SSet.yonedaEquiv.{0}.symm z.down).op
  rw [← SSet.yonedaEquiv_symm_comp z.down g, op_comp,
    (simplicialConvolution R B).map_comp, Category.assoc]

lemma smallMultiplicativeMappingCurry_postcompose {A B C : Mon (Complex R)} {K : SSet.{0}}
    (f : A ⟶ (simplicialConvolution R B).obj (op K)) (q : B ⟶ C) :
    smallMultiplicativeMappingCurry R f ≫ multiplicativeMappingPostcompose R A q =
      smallMultiplicativeMappingCurry R
        (f ≫ (simplicialConvolutionTargetNatTrans R q).app (op K)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change ULift.{u, 0} (K.obj n) at z
  let σ := SSet.yonedaEquiv.{0}.symm z.down
  change (f ≫ (simplicialConvolution R B).map σ.op) ≫
      (simplicialConvolutionTargetNatTrans R q).app (op (SSet.stdSimplex.obj n.unop)) =
    (f ≫ (simplicialConvolutionTargetNatTrans R q).app (op K)) ≫
      (simplicialConvolution R C).map σ.op
  simpa only [Category.assoc] using congrArg (fun t => f ≫ t)
    ((simplicialConvolutionTargetNatTrans R q).naturality σ.op)

set_option maxHeartbeats 800000 in -- 元の AW 余単位の制限を、指定底の全単体の定数射へ照合する。
lemma smallMultiplicativeMappingCurry_constant {A B : Mon (Complex R)} {K : SSet.{0}}
    (s : A ⟶ B) :
    smallMultiplicativeMappingCurry R (s ≫ (simplicialConvolutionConstant R B).app (op K)) =
      SSet.stdSimplex.isTerminalObj₀.from (SSet.uliftFunctor.{u, 0}.obj K) ≫
        multiplicativeMappingBase R s := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  change ULift.{u, 0} (K.obj n) at z
  change (s ≫ convolutionConstantMap R
      ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor R).obj K) B) ≫
      convolutionPrecompose R
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComonFunctor R).map
          (SSet.yonedaEquiv.{0}.symm z.down)) B =
    s ≫ convolutionConstantMap R (simplexComonoid R n.unop) B
  rw [Category.assoc, convolutionConstantMap_precompose]
  rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
