module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagVertexRecovery

/-!
概要：同じ全多次数の wide 成分上で元の始域像への所属を判定する。
方針：分母辺の両端で像所属が一致することから、成分集合上の述語へ降ろす。
規約：成分集合を K₀ の商群と未証明のまま同一視しない。
使われ方：相対旗が元の始域旗へ回収できることの離散的障害。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の本質像所属は同じ wide 模型の成分集合上の述語を定める。
方針：成分への射の普遍性へ像所属の辺不変性を渡す。
規約：本質像は同じ元の反復 S 射の本質像である。
使われ方：始域像の成分を離散的に判定する障害条件。 -/
def completionWideImageComponent (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) → Prop :=
  SSet.π₀.lift (fun x => x.val ∈ LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val) (fun {_ _} e =>
      propext (completionMultiWideComponent_image_iff r ι f hf _ _ (SSet.π₀.sound e)))

/-- 概要：成分上の像述語は各頂点で元の本質像条件を厳密に回収する。
方針：成分への降下の定義を計算する。
規約：同じ wide の頂点を使う。
使われ方：具体的な相対旗の一頂点で障害を検査する。 -/
lemma completionWideImageComponent_mk (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌) :
    completionWideImageComponent r ι f hf (SSet.π₀.mk x) ↔
      x.val ∈ LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val := Iff.rfl

/-- 概要：連結な旗では、離散的な像成分の障害は評価頂点の選択に依存しない。
方針：パラメータの成分の一意性を元の wide への旗で写す。
規約：旗全体の同じ持ち上げを使用する。
使われ方：相対旗の任意の一頂点での障害判定。 -/
lemma completionWideFlag_component_independent (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    {K : SSet.{u}} [K.IsPreconnected]
    (g : K ⟶ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) (k l : K _⦋0⦌) :
    SSet.π₀.mk (g.app (Opposite.op ⦋0⦌) k) =
      SSet.π₀.mk (g.app (Opposite.op ⦋0⦌) l) :=
  congrArg (SSet.mapπ₀ g) (Subsingleton.elim (SSet.π₀.mk k) (SSet.π₀.mk l))

/-- 概要：連結な相対旗は指定した wide 成分が像成分であるとき、かつそのときだけ回収できる。
方針：全体の持ち上げの一頂点で像条件を照合し、既存の相対旗内の同型判定を使う。
規約：障害の消滅は元の始域旗との同じ相対旗圏内の同型を意味する。
使われ方：相対 fiber 比較での始域側の離散的な判定。 -/
theorem completionRelativeFlag_recovery_iff_imageComponent (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected]
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌)
    (g : K ⟶ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}))
    (hg : g ≫ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val).ι =
      completionRelativeFlagVertexFunctor r ι f hf v) (k : K _⦋0⦌) :
    (∃ s : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K).app
        (Opposite.op ⦋0⦌) s) v)) ↔
      completionWideImageComponent r ι f hf (SSet.π₀.mk (g.app (Opposite.op ⦋0⦌) k)) := by
  have he := congrArg (fun q : K ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier =>
    q.app (Opposite.op ⦋0⦌) k) hg
  have hp := congrArg (fun y => y ∈ LocalizingInvariants.completionEssentialImage
    (((multiSEndofunctor r).obj ι).map f).val) he
  exact (completionSourceFlagVertexImage_iff r ι f hf v k).trans (Iff.of_eq hp.symm)

end SerrePositivity.KST.SConstruction.Cofinality
