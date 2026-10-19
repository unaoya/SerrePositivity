module

public import SerrePositivity.KST.Comparison.LocalCoefficientDegreeComparison
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# 基底上の局所係数複体の余極限と単射の保存

概要：基底上の局所係数複体が余極限と単射を保存することを証明する。
方針：各次数で係数の直和の左随伴と比較し、単体的群の評価で判定する。
規約：Weibel K-book IV.1.6 の horn 添付。正規化では実際の Dold–Kan 同値を使う。
使われ方：局所係数での pushout と超限合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

/--
概要：基底上の単体次数への評価は余極限を保存する。
方針：slice の忘却が余極限を作ることと、単体集合の評価の余極限保存を使う。
規約：基底も同じ次数で評価する。
使われ方：局所係数の次数ごとの左随伴への帰着。
-/
instance overSimplicialEvaluation_preservesColimits (B : SSet.{u}) (d : SimplexCategoryᵒᵖ) :
    PreservesColimitsOfSize.{u, u} (overSimplicialEvaluation B d) := by
  have : PreservesColimitsOfSize.{u, u}
      (overSimplicialEvaluation B d ⋙ Over.forget (B.obj d)) := by
    change PreservesColimitsOfSize.{u, u}
      (Over.forget B ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj d)
    infer_instance
  exact preservesColimits_of_reflects_of_preserves _ (Over.forget (B.obj d))

/--
概要：基底上の単体次数への評価は単射を保存する。
方針：基底上の射の単射性を下の単体写像とその各次数で判定する。
規約：slice の射の単射性。
使われ方：係数群の直和の単射保存への接続。
-/
instance overSimplicialEvaluation_preservesMonomorphisms (B : SSet.{u})
    (d : SimplexCategoryᵒᵖ) : (overSimplicialEvaluation B d).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have : Mono (f.left.app d) := (NatTrans.mono_iff_mono_app f.left).mp inferInstance d
    have : Mono (((overSimplicialEvaluation B d).map f).left) := this
    exact Over.mono_of_mono_left _

/--
概要：基底上の局所係数の単体的群の関手は余極限を保存する。
方針：各次数で基底上の評価と係数直和の左随伴の合成へ自然同型で移す。
規約：全ての指定宇宙の余極限。
使われ方：セル添付の pushout と余極限。
-/
instance overLocalCoefficientSimplicialFunctor_preservesColimits {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    PreservesColimitsOfSize.{u, u} (overLocalCoefficientSimplicialFunctor L) where
  preservesColimitsOfShape {_J} _ :=
    preservesColimitsOfShape_of_evaluation _ _ (fun d =>
      preservesColimitsOfShape_of_natIso (overLocalCoefficientDegreeIso L d).symm)

/--
概要：基底上の局所係数の単体的群の関手は単射を保存する。
方針：各次数で係数直和の単射保存へ自然同型で移す。
規約：係数群の平坦性を要求しない。
使われ方：局所係数複体の単射性。
-/
instance overLocalCoefficientSimplicialFunctor_preservesMonomorphisms {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    (overLocalCoefficientSimplicialFunctor L).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have (d : SimplexCategoryᵒᵖ) :
        Mono (((overLocalCoefficientSimplicialFunctor L).map f).app d) := by
      have : (overLocalCoefficientSimplicialFunctor L ⋙
          (evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj d).PreservesMonomorphisms :=
        Functor.PreservesMonomorphisms.of_iso (overLocalCoefficientDegreeIso L d).symm
      exact (overLocalCoefficientSimplicialFunctor L ⋙
        (evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{u}).obj d).map_mono f
    exact NatTrans.mono_of_mono_app _

/--
概要：アーベル群の正規化 Moore 複体の関手は実際の圏同値である。
方針：Mathlib の Dold–Kan 同値の順関手との定義的な一致を使う。
規約：単体的アーベル群と非負鎖複体の同値。
使われ方：正規化の余極限と単射の保存。
-/
instance normalizedMooreComplexAb_isEquivalence :
    (normalizedMooreComplex AddCommGrpCat.{u}).IsEquivalence :=
  (CategoryTheory.Abelian.DoldKan.equivalence (A := AddCommGrpCat.{u})).isEquivalence_functor

/--
概要：基底上の局所係数の正規化鎖複体は余極限を保存する。
方針：単体的群の余極限保存と Dold–Kan 同値の余極限保存を合成する。
規約：全ての指定宇宙の余極限。
使われ方：局所係数のセル添付の複体。
-/
instance overLocalCoefficientChainsFunctor_preservesColimits {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    PreservesColimitsOfSize.{u, u} (overLocalCoefficientChainsFunctor L) := by
  dsimp only [overLocalCoefficientChainsFunctor]
  infer_instance

/--
概要：基底上の局所係数の正規化鎖複体は単射を保存する。
方針：単体的群の単射保存と正規化の圏同値を合成する。
規約：全ての基底上の単射。
使われ方：単射な局所係数鎖写像の pushout。
-/
instance overLocalCoefficientChainsFunctor_preservesMonomorphisms {B : SSet.{u}}
    (L : LocalCoefficientSystem B) :
    (overLocalCoefficientChainsFunctor L).PreservesMonomorphisms := by
  dsimp only [overLocalCoefficientChainsFunctor]
  infer_instance

end SerrePositivity.KST.Comparison
