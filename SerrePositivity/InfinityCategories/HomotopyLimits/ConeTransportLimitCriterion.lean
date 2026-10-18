module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSectionLimitCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.TransportSectionsComparison

/-!
概要：錐の表現可能な left fibration の strict transport の end による ∞ 極限判定。
方針：切断空間への表現可能な比較に、切断と transport の標準比較を合成する。
規約：豊穣 Hom の元の図式との比較は別に必要。ここでは実際の transport 図式を使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の三つの極限の切断模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：錐の表現可能な left fibration の strict transport の end は Kan 複体。
方針：transport の各値の Kan 性と Bousfield–Kan end の一般の Kan 性を使う。
規約：通常の小圏 I は任意である。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の end での表現可能な比較の同値判定。 -/
instance coneTransportHolim_kanComplex {I : Type u} [SmallCategory I]
    {X : SSet.{u}} [Quasicategory X] (p : nerve I ⟶ X) (x : X _⦋0⦌) :
    KanComplex (bousfieldKanHolim (leftStrictTransportDiagram (coherentConeProjection p x))) := by
  have : ∀ i : I, KanComplex
      ((leftStrictTransportDiagram (coherentConeProjection p x)).obj i) :=
    fun i => leftStrictTransport_kanComplex (coherentConeProjection p x) i
  exact bousfieldKanHolim_kanComplex _

/-- 概要：底の pinched Hom から錐の left fibration の transport の end への実際の比較。
方針：切断空間への表現可能な比較、引き戻しの切断の同型、標準の end の比較を合成する。
規約：逆射の選択を含み、元の豊穣 q_x とまだ同一視しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の極限検出と end 模型の接続。 -/
noncomputable def coneTransportHomComparison {I : Type u} [SmallCategory I]
    {X : SSet.{u}} [Quasicategory X] {p : nerve I ⟶ X} (c : JoinCone p) (x : X _⦋0⦌) :
    pinchedHom x c.vertex ⟶
      bousfieldKanHolim (leftStrictTransportDiagram (coherentConeProjection p x)) :=
  coneSectionHomComparison c x ≫ (coherentConeSectionsIso p x).inv ≫
    strictTransportSectionsComparison (coherentConeProjection p x)

/-- 概要：切断と transport の標準比較が同値なら、end への表現可能な比較の同値性も同じ条件。
方針：切断模型の厳密な同型と標準比較の同値性から二対三則を使う。
規約：この補題の標準比較の同値性は明示的な仮定である。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の各形状での実際の end の判定。 -/
lemma coneTransportHomComparison_homotopyEquivalence_iff {I : Type u} [SmallCategory I]
    {X : SSet.{u}} [Quasicategory X] {p : nerve I ⟶ X} (c : JoinCone p) (x : X _⦋0⦌)
    (hκ : IsSimplicialHomotopyEquivalence
      (strictTransportSectionsComparison (coherentConeProjection p x))) :
    IsSimplicialHomotopyEquivalence (coneTransportHomComparison c x) ↔
      IsSimplicialHomotopyEquivalence (coneSectionHomComparison c x) := by
  have := simplicialSections_kanComplex (coherentConeProjection p x)
  have he := (qCatEquivalenceOfIso (coherentConeSectionsIso p x).symm).isQCatEquivalence.comp
    hκ.isQCatEquivalence
  constructor
  · intro h
    exact (he.cancel_right h.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro h
    exact (h.isQCatEquivalence.comp he).isSimplicialHomotopyEquivalence

/-- 概要：全頂点で切断と transport の比較が同値なら、錐の極限性を transport の end で検出できる。
方針：切断空間での極限判定と各頂点の二対三則を合わせる。
規約：標準比較の同値性はこの一般形の仮定として明示する。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の具体的な形状への共通の推論。 -/
lemma isLimitCone_iff_coneTransportHomComparison_of_transport {I : Type u} [SmallCategory I]
    {X : SSet.{u}} [Quasicategory X] {p : nerve I ⟶ X} (c : JoinCone p)
    (hκ : ∀ x : X _⦋0⦌, IsSimplicialHomotopyEquivalence
      (strictTransportSectionsComparison (coherentConeProjection p x))) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneTransportHomComparison c x) := by
  rw [isLimitCone_iff_coneSectionHomComparison_homotopyEquivalence]
  apply forall_congr'
  intro x
  exact (coneTransportHomComparison_homotopyEquivalence_iff c x (hκ x)).symm

/-- 概要：cospan の錐の極限性は全頂点での表現可能な transport の end の比較で検出できる。
方針：left fibration の cospan の切断と end の実際の同値を一般判定へ渡す。
規約：p の fibration 性などの追加の比較仮定は置かない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の引き戻しの native な end 判定。 -/
lemma isLimitCone_iff_coneTransportHomComparison_cospan {X : SSet.{u}} [Quasicategory X]
    {p : nerve (AsSmall.{u} WalkingCospan) ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneTransportHomComparison c x) :=
  isLimitCone_iff_coneTransportHomComparison_of_transport c
    (fun x => strictTransportSectionsComparison_cospan_homotopyEquivalence
      (coherentConeProjection p x))

/-- 概要：塔の錐の極限性は全頂点での表現可能な transport の end の比較で検出できる。
方針：left fibration の塔の切断と end の実際の同値を一般判定へ渡す。
規約：添字は AsSmall.{u} ℕᵒᵖ。p に追加の仮定は不要。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の逆極限の native な end 判定。 -/
lemma isLimitCone_iff_coneTransportHomComparison_tower {X : SSet.{u}} [Quasicategory X]
    {p : nerve (AsSmall.{u} ℕᵒᵖ) ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneTransportHomComparison c x) :=
  isLimitCone_iff_coneTransportHomComparison_of_transport c
    (fun x => strictTransportSectionsComparison_tower_homotopyEquivalence
      (coherentConeProjection p x))

/-- 概要：離散図式の錐の極限性は全頂点での表現可能な transport の end の比較で検出できる。
方針：離散図式の切断と end の比較の厳密な同型を一般判定へ渡す。
規約：添字 J の有限性も非空性も要求しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6 の積の native な end 判定。 -/
lemma isLimitCone_iff_coneTransportHomComparison_discrete {J : Type u}
    {X : SSet.{u}} [Quasicategory X] {p : nerve (Discrete J) ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (coneTransportHomComparison c x) := by
  apply isLimitCone_iff_coneTransportHomComparison_of_transport c
  intro x
  have := simplicialSections_kanComplex (coherentConeProjection p x)
  have := strictTransportSectionsComparison_discrete_isIso (coherentConeProjection p x)
  have he := (qCatEquivalenceOfIso
    (asIso (strictTransportSectionsComparison (coherentConeProjection p x)))).isQCatEquivalence
  exact he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
