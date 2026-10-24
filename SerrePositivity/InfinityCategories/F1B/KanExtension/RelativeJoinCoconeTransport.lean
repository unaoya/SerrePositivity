module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinShiftPrism
public import SerrePositivity.InfinityCategories.F1B.KanExtension.ComparisonCartesian

/-!
概要：相対 join の局所余錐を指定自然変換の比較余錐として表示する。
方針：持ち上げた prism を図式で写し、四境界を輸送のフィールドへ渡す。
規約：輸送の存在を追加仮定せず、実際の族を構成する。
使われ方：相対 join 上の左 Kan 条件と点ごとの局所余極限性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 join 上の図式の標準 prism が与える指定自然変換。
方針：時間を第二因子へ直し、両端の計算則を使う。
規約：変換の向きは左端から右端の δ に沿う制限。
使われ方：局所比較余錐の指定変換。 -/
def kanRelativeJoinTransformation {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : relativeJoin δ (𝟙 C) ⟶ D) :
    SSet.Homotopy (relativeJoinInl δ (𝟙 C) ≫ G) (δ ≫ relativeJoinInr δ (𝟙 C) ≫ G) where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ relativeJoinPrism δ ≫ G
  h₀ := by
    rw [← Category.assoc]
    change prismEndpoint 0 K ≫ relativeJoinPrism δ ≫ G = _
    rw [← Category.assoc, relativeJoinPrism_zero]
    rfl
  h₁ := by
    rw [← Category.assoc]
    change prismEndpoint 1 K ≫ relativeJoinPrism δ ≫ G = _
    rw [← Category.assoc, relativeJoinPrism_one, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：相対 join の局所余錐から、指定変換に両立する実際の輸送を構成する。
方針：slice の普遍余錐の移動 prism に G を後合成し、四境界を計算する。
規約：D の quasicategory 性を構成には要求しない。
使われ方：局所余錐の余極限性を左 Kan 条件へ移す。 -/
def kanRelativeJoinCoconeTransport {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    LeftKanCoconeTransport δ (relativeJoinInl δ (𝟙 C) ≫ G)
      (relativeJoinInr δ (𝟙 C) ≫ G) (kanRelativeJoinTransformation δ G) c where
  family := kanRelativeJoinShiftPrism δ (leftKanProjection δ c)
    (sliceOverUncurry (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c))))
    (by rw [sliceOverUncurry_projection, ← pullback.condition]) ≫ G
  finish := by
    rw [← Category.assoc, kanRelativeJoinShiftPrism_one]
    rfl
  diagram := by
    rw [← Category.assoc, kanRelativeJoinShiftPrism_left]
    have h : (β_ (Δ[1] : SSet.{u}) (leftKanShape δ c)).hom ≫
        (leftKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫
        (β_ K (Δ[1] : SSet.{u})).hom = ((Δ[1] : SSet.{u}) ◁ leftKanProjection δ c) := rfl
    simpa only [kanRelativeJoinTransformation, Category.assoc] using
      (congrArg (fun q ↦ q ≫ relativeJoinPrism δ ≫ G) h).symm
  fixedVertex := by
    rw [← Category.assoc, kanRelativeJoinShiftPrism_right]
    rfl

/-- 概要：構成した輸送の比較余錐は、元の相対 join の局所余錐と同じ射を持つ。
方針：移動 prism の始点を計算し、slice の固定端の式を使う。
規約：添字図式の表示の違いを避けて raw な射の等式で述べる。
使われ方：余極限性を両表示の間で移す。 -/
lemma kanRelativeJoinCoconeTransport_cocone_val {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinCoconeTransport δ G c).cocone.val =
      (kanRelativeJoinDiagramCocone δ c G).val := by
  change prismEndpoint 0 _ ≫ (kanRelativeJoinShiftPrism δ (leftKanProjection δ c)
    (sliceOverUncurry (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c)))) _ ≫ G) = _
  rw [← Category.assoc, kanRelativeJoinShiftPrism_zero]
  simp only [sliceOverUncurry_fixed]
  rfl

/-- 概要：構成した輸送の比較余錐は相対 join の局所余錐に等しい。
方針：raw な射の同一性から部分型の外延性を使う。
規約：添字図式の定義を展開した同じ部分型で比較する。
使われ方：左 Kan 条件と局所余極限性の同値。 -/
lemma kanRelativeJoinCoconeTransport_cocone {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : relativeJoin δ (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinCoconeTransport δ G c).cocone = kanRelativeJoinDiagramCocone δ c G :=
  Subtype.ext (kanRelativeJoinCoconeTransport_cocone_val δ G c)

/-- 概要：相対 join の標準指定変換の左 Kan 条件は局所余錐の余極限性と同値。
方針：実際の局所輸送と、比較余錐の選択不変性を合わせる。
規約：D の quasicategory 性を使うが δ の単射性は不要。
使われ方：点ごとの定義を相対 join 上の図式の制限として扱う。 -/
lemma isLeftKanExtension_relativeJoin_iff_local_colimits {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (G : relativeJoin δ (𝟙 C) ⟶ D) :
    IsLeftKanExtension δ (relativeJoinInl δ (𝟙 C) ≫ G) (relativeJoinInr δ (𝟙 C) ≫ G)
      (kanRelativeJoinTransformation δ G) ↔
      ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinDiagramCocone δ c G) := by
  constructor
  · intro h c
    have ht := (isLeftKanExtension_iff_forall_transport δ _ _ _).1 h c
      (kanRelativeJoinCoconeTransport δ G c)
    rwa [kanRelativeJoinCoconeTransport_cocone] at ht
  · intro h c
    refine ⟨kanRelativeJoinCoconeTransport δ G c, ?_⟩
    rw [kanRelativeJoinCoconeTransport_cocone]
    exact h c

end SerrePositivity.InfinityCategories
