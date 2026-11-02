module

public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeFunctorUnitPrism

/-!
概要：指定形状の余極限が全て存在するとき、その余極限を全関手として選ぶ。
方針：普遍余錐の射影の切断を選び、全余錐を頂点で評価する。
規約：全単体に自然な余錐族を同時に保持する。
使われ方：有限余積の比較を Yoneda 生成対象から全対象へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable (K X : SSet.{u}) [Quasicategory X] (hX : ∀ p : K ⟶ X, HasColimit p)

include hX in
/-- 概要：元の全図式を厳密に保持する普遍余錐族の切断が存在する。
方針：恒等図式族に各頂点の余極限存在を適用する。
規約：元の図式圏に quasicategory 性を追加しない。
使われ方：余極限関手の関手的選択。 -/
lemma exists_chosenColimitSection :
    ∃ s : (ihom K).obj X ⟶ colimitCocones K X,
      s ≫ colimitCoconeProjection K X = 𝟙 _ :=
  exists_colimitCoconeFamily (𝟙 _) (fun v ↦ hX ((functorVertexEquiv K X).symm v))

/-- 概要：全図式の普遍余錐を同時に選ぶ切断。
方針：構成した全切断の存在から一つを選ぶ。
規約：切断の選択を全次数で共通にする。
使われ方：元の余極限関手と比較射の構成。 -/
def chosenColimitSection : (ihom K).obj X ⟶ colimitCocones K X :=
  Classical.choose (exists_chosenColimitSection K X hX)

/-- 概要：選んだ切断は元の全図式を厳密に回収する。
方針：切断の選択の証明を使う。
規約：全単体の等式である。
使われ方：単位の始端条件。 -/
lemma chosenColimitSection_projection :
    chosenColimitSection K X hX ≫ colimitCoconeProjection K X = 𝟙 _ :=
  Classical.choose_spec (exists_chosenColimitSection K X hX)

/-- 概要：選んだ全普遍余錐を元の余錐の関手圏へ含める。
方針：同じ全部分複体の包含を後合成する。
規約：元の全余錐を保持する。
使われ方：余極限関手と全単位の構成。 -/
def chosenColimitCoconeFamily : (ihom K).obj X ⟶ (ihom (join K Δ[0])).obj X :=
  chosenColimitSection K X hX ≫ (relativeInitialVertices (coconeRestriction K X)).ι

/-- 概要：選んだ全余錐の左端は元の全図式族である。
方針：普遍余錐射影の厳密な切断条件を使う。
規約：全単体の等式である。
使われ方：元の図式を保つ全余錐。 -/
lemma chosenColimitCoconeFamily_restrict :
    chosenColimitCoconeFamily K X hX ≫ coconeRestriction K X = 𝟙 _ :=
  chosenColimitSection_projection K X hX

/-- 概要：選んだ余極限の実際の全関手。
方針：全普遍余錐族を同じ右頂点で評価する。
規約：頂点ごとの独立した選択ではない。
使われ方：有限余積を関手として比較する。 -/
def chosenColimitFunctor : (ihom K).obj X ⟶ X :=
  chosenColimitCoconeFamily K X hX ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInr K Δ[0]))

/-- 概要：選んだ余極限関手と定値関手の間の全単位。
方針：全普遍余錐族の円柱を用い、厳密な制限条件で始端を揃える。
規約：元の全図式を始端に保持する。
使われ方：余極限と定値図式の随伴。 -/
def chosenColimitUnit : SSet.Homotopy (𝟙 ((ihom K).obj X))
    (chosenColimitFunctor K X hX ≫ constantFunctorMap K X) where
  h := coconeFunctorUnitPrism (chosenColimitCoconeFamily K X hX)
  h₀ := (coconeFunctorUnitPrism_zero _).trans (chosenColimitCoconeFamily_restrict K X hX)
  h₁ := coconeFunctorUnitPrism_one _
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, t⟩
    exact False.elim hx

/-- 概要：選んだ全余錐族を指定図式の全余錐として取り出す。
方針：族の零単体を全関手へ戻し、切断条件で図式を照合する。
規約：指定した図式を厳密に保つ。
使われ方：単位成分の普遍性の判定。 -/
def chosenColimitCocone (p : K ⟶ X) : JoinCocone p := by
  let q := (functorVertexEquiv (join K Δ[0]) X).symm
    ((chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p))
  refine ⟨q, ?_⟩
  apply (functorVertexEquiv K X).injective
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (chosenColimitCoconeFamily_restrict K X hX) (Opposite.op ⦋0⦌))
      (functorVertex p)
  have hq : functorVertex q =
      (chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change (coconeRestriction K X).app (Opposite.op ⦋0⦌)
    ((chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p)) =
      functorVertex p at h
  rw [← hq] at h
  exact h

/-- 概要：選んだ指定全余錐は余極限である。
方針：普遍余錐全部分複体の頂点条件を native な余極限性へ戻す。
規約：同じ選択した全余錐を使う。
使われ方：各点の単位の普遍性。 -/
lemma chosenColimitCocone_isColimit (p : K ⟶ X) :
    IsColimitCone (chosenColimitCocone K X hX p) := by
  apply (isColimitCone_iff_initialBoundaryLifting _).mpr
  have h := fullSubcomplexOnVertices_vertex
    ((chosenColimitSection K X hX).app (Opposite.op ⦋0⦌) (functorVertex p))
  change InitialBoundaryLifting (coconeRestriction K X)
    (functorVertex ((functorVertexEquiv (join K Δ[0]) X).symm
      ((chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p))))
  have hrec : functorVertex ((functorVertexEquiv (join K Δ[0]) X).symm
      ((chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p))) =
      (chosenColimitCoconeFamily K X hX).app (Opposite.op ⦋0⦌) (functorVertex p) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [hrec]
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
