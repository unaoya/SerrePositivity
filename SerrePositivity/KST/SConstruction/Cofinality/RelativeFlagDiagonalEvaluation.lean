module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeCoreEvaluation

/-!
概要：同じ全多次数の相対 core 旗の対角実現から元の wide 部分圏へ評価する。
方針：旗パラメータの恒等単体と core 単体を全評価へ渡す。
規約：射を構成するが、その弱同値性や相対 fiber 比較は別に証明する。
使われ方：相対 S• 実現と Sp-7 の亜群化の間の具体的な比較射。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：実供給による相対旗の core を旗方向の単体的図式に束ねる。
方針：構成済みの全旗図式と core 関手を合成する。
規約：同じ全多次数を固定し、元の ambient 相対旗を使う。
使われ方：相対旗の対角実現の入力。 -/
def completionRelativeCoreFlagDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  ((completionRelativeFlagDiagram r f hf).obj ι) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：同じ S 多次数の相対 core 旗の未置換対角実現。
方針：旗方向と core 方向に既存の対角関手を適用する。
規約：この対角に Kan 性を主張しない。
使われ方：相対実現の亜群化との比較の始域。 -/
def completionRelativeFlagRealization (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) : SSet.{u} :=
  simplicialDiagonalFunctor.obj (completionRelativeCoreFlagDiagram r ι f hf)

/-- 概要：相対旗の対角実現を同じ元の S 対象へ評価する。
方針：全評価へ標準 n 単体の恒等単体を代入する。
規約：全ての高次単体の自然性を検査する。
使われ方：wide 比較の包含後の元の射。 -/
def completionRelativeFlagEvaluation (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeFlagRealization r ι f hf ⟶
      (((multiSEndofunctor r).obj ι).obj Y).carrier where
  app n := ↾fun v => v.val.val.app n (𝟙 n) (ULift.up (𝟙 n.unop))
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro v
    let V : ((ihom (SSet.stdSimplex.obj n.unop)).obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier).obj n := v.val.val
    have h := ConcreteCategory.congr_hom (V.naturality α (𝟙 n))
      (SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
    exact h

/-- 概要：相対旗の対角実現を Sp-7 の元の wide 部分複体へ評価する。
方針：全評価の wide 因子化に恒等単体を代入する。
規約：弱同値性を追加の証明なしに結論しない。
使われ方：相対実現の離散性を検査する具体的な射。 -/
def completionRelativeFlagWideEvaluation (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeFlagRealization r ι f hf ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) where
  app n := ↾fun v =>
    (completionRelativeCoreEvaluationWide r ι f hf (SSet.stdSimplex.obj n.unop)).app n
      (ULift.up (𝟙 n.unop), v)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    let V : ((ihom (SSet.stdSimplex.obj n.unop)).obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier).obj n := v.val.val
    have h := ConcreteCategory.congr_hom (V.naturality α (𝟙 n))
      (SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
    exact h

/-- 概要：wide 対角評価は包含後に元の相対旗の全対角評価を回収する。
方針：全評価の持ち上げの定義を計算する。
規約：未置換の射の厳密な等号。
使われ方：元の相対 S• 図式との射の照合。 -/
lemma completionRelativeFlagWideEvaluation_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionRelativeFlagWideEvaluation r ι f hf ≫
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).ι =
      completionRelativeFlagEvaluation r ι f hf := rfl

/-- 概要：対角評価の零単体は元の未置換零段比較の頂点評価そのもの。
方針：標準零単体で恒等単体と一点の頂点を照合する。
規約：元の S 対象への射を厳密に保持する。
使われ方：元の K 射を含む零段比較と対角評価の接続。 -/
lemma completionRelativeFlagEvaluation_zero (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (v : (completionRelativeFlagRealization r ι f hf) _⦋0⦌) :
    (completionRelativeFlagEvaluation r ι f hf).app (Opposite.op ⦋0⦌) v =
      (completionRelativeFlagZeroIso r ι f hf).hom.app (Opposite.op ⦋0⦌) v.val := by
  change v.val.val.app (Opposite.op ⦋0⦌) (𝟙 _) (ULift.up (𝟙 ⦋0⦌)) =
    v.val.val.app (Opposite.op ⦋0⦌) (𝟙 _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 0)
  have hs : (ULift.up (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 0 := by
    apply SSet.stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  exact congrArg (fun k => v.val.val.app (Opposite.op ⦋0⦌) (𝟙 _) k) hs

/-- 概要：現在の評価射は標準単体の対角による制限そのものである。
方針：旗の n 単体を uncurry し、二つの恒等単体で評価する。
規約：端点評価や行射影ではなく Δ[n] から Δ[n]×Δ[n] への対角を使う。
使われ方：Sp-8 の対角制限との厳密な照合。 -/
lemma completionRelativeFlagEvaluation_eq_diagonalRestriction (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ)
    (v : (completionRelativeFlagRealization r ι f hf) _⦋n⦌) :
    (completionRelativeFlagEvaluation r ι f hf).app (Opposite.op ⦋n⦌) v =
      SSet.yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 (Δ[n] : SSet.{u})) (𝟙 _) ≫
        uncurry (SSet.yonedaEquiv.symm v.val.val)) := rfl

end SerrePositivity.KST.SConstruction.Cofinality
