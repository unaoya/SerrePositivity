module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyne
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
public import SerrePositivity.InfinityCategories.F2.WeakHomotopyPrecomposition

/-!
概要：任意の弱ホモトピー同値は、同じ実際の写像の任意の宇宙持ち上げでも弱同値。
方針：anodyne な連続 Kan 置換と Kan 間の同値の宇宙移送で二対三則を使う。
規約：元の二対象の Kan 性も、単体集合のモデル圏構造の追加仮定も要求しない。
使われ方：元の小さい全空間余極限の単位を、大きい空間値の余極限判定へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の anodyne 射を持ち上げた同じ写像は、大きい全 Kan 標的で弱同値。 -/
lemma weakHomotopyEquivalence_ulift_of_anodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : anodyneExtensions f) :
    IsWeakHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) := by
  intro Z hZ
  exact (HomotopyLimits.homotopyEquivalence_pre_of_anodyne _
    (SimplicialModel.UniverseLift.anodyne_map f hf) Z).mapPiZero_bijective

/-- 元の任意の弱ホモトピー同値は、任意の宇宙へ同じ射として持ち上がる。 -/
lemma weakHomotopyEquivalence_ulift {A B : SSet.{u}} (f : A ⟶ B)
    (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) := by
  let U := SSet.uliftFunctor.{v, u}
  have hA := weakHomotopyEquivalence_ulift_of_anodyne.{u, v}
    (continuousKanReplacementUnit.app A) (continuousKanReplacementUnit_anodyne A)
  have hB := weakHomotopyEquivalence_ulift_of_anodyne.{u, v}
    (continuousKanReplacementUnit.app B) (continuousKanReplacementUnit_anodyne B)
  have hK₀ := (IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
    (continuousKanReplacement_map_isWeakHomotopyEquivalence f hf)).isQCatEquivalence
  have hK := (IsQCatEquivalence.ulift.{u, v} hK₀).isWeakHomotopyEquivalence
  have hn := congrArg U.map (continuousKanReplacementUnit.naturality f)
  simp only [Functor.map_comp, Functor.id_map] at hn
  dsimp only [U] at hn
  apply hB.cancel_right
  rw [hn]
  exact hA.comp hK

/-- 全自然同型で比較される元の二射は、任意の Kan 標的に対し同時に弱同値。 -/
lemma weakHomotopyEquivalence_iff_of_functorIso {A B : SSet.{u}} {f g : A ⟶ B}
    (e : FunctorIso f g) : IsWeakHomotopyEquivalence f ↔ IsWeakHomotopyEquivalence g := by
  have he (Z : SSet.{u}) [KanComplex Z] :
      SSet.mapπ₀ ((pre f).app Z) = SSet.mapπ₀ ((pre g).app Z) :=
    funext (mapPiZero_eq_of_homotopy (FunctorIso.simplicialHomotopy (e.map_pre Z)))
  constructor
  · intro hf Z hZ
    rw [← he Z]
    exact hf Z
  · intro hg Z hZ
    rw [he Z]
    exact hg Z

end SerrePositivity.InfinityCategories.F2.Compact
