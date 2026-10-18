module

public import SerrePositivity.InfinityCategories.DoldKanComparison.ResolutionHornPositiveFace
public import SerrePositivity.InfinityCategories.Core.PrecompositionHomotopy

/-!
# Kan 複体を標的とする前合成の同値判定

概要：任意の Kan 複体への写像空間で前合成が実際のホモトピー同値になる条件を扱う。
方針：関手単体集合も Kan であることにより、向き付きホモトピーから可逆な二胞体を得る。
規約：始域の補助解像には Kan 性を要求せず、モデル構造の存在の引用を使わない。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23 の相対的な解像の位相的比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

/-- 概要：標的が Kan なら任意の単体的ホモトピーは前合成作用の可逆な二胞体を与える。
方針：前合成の辺を内部 Hom に写し、そのホモトピー圏の全ての射の可逆性を使う。
規約：元の始域・終域には Kan 性を仮定しない。
使われ方：Kerodon §4.5.1、解像の向き付き変形を写像空間の同値に使う。 -/
def functorIsoPrecompositionOfHomotopyKan {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (K : SSet.{u}) [KanComplex K] :
    FunctorIso ((pre f).app K) ((pre g).app K) := by
  let q := functorPrecompositionMap A B K
  let e := functorEdgeOfSimplicialHomotopy H
  let m : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj K)).obj ((ihom A).obj K)))
      (functorVertex ((pre f).app K)) (functorVertex ((pre g).app K)) :=
    { edge := q.app (Opposite.op ⦋1⦌) e.edge
      src_eq := (e.map ((truncation 2).map q)).src_eq.trans (functorPrecompositionMap_vertex f)
      tgt_eq := (e.map ((truncation 2).map q)).tgt_eq.trans (functorPrecompositionMap_vertex g) }
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk m) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj ((ihom ((ihom B).obj K)).obj ((ihom A).obj K)))
      (SSet.Truncated.HomotopyCategory.homMk m)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk m)

/-- 概要：全ての Kan 複体への写像空間の前合成が実際のホモトピー同値になる条件。
方針：標準の内部 Hom と既存の単体的ホモトピー同値性を使う。
規約：一般の quasicategory を標的とする強い条件とは別に定義する。
使われ方：Kerodon Proposition 4.6.7.23 の解像の位相的な同値判定。 -/
def IsKanPrecompositionEquivalence {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∀ (K : SSet.{u}) [KanComplex K], IsSimplicialHomotopyEquivalence ((pre f).app K)

/-- 概要：一般の quasicategory への前合成の同値性は Kan 標的の判定を含む。
方針：Kan 複体で試し、Kan な内部 Hom 間の同値を実際のホモトピー逆へ戻す。
規約：元の二つの単体集合の充填性は不要。
使われ方：Kerodon Proposition 4.6.7.23 の F1 の確定済みの面上の比較の適用。 -/
lemma isKanPrecompositionEquivalence_of_precompositionEquivalence {A B : SSet.{u}} {f : A ⟶ B}
    (hf : IsPrecompositionEquivalence f) : IsKanPrecompositionEquivalence f := by
  intro K hK
  exact (hf K).isSimplicialHomotopyEquivalence

/-- 概要：恒等射は Kan 標的の前合成の同値条件を満たす。
方針：一般の前合成の恒等射の判定を制限する。
規約：単体集合 A は任意。
使われ方：Kerodon §4.5.1 の変形の基底。 -/
lemma isKanPrecompositionEquivalence_id (A : SSet.{u}) :
    IsKanPrecompositionEquivalence (𝟙 A) :=
  isKanPrecompositionEquivalence_of_precompositionEquivalence (isPrecompositionEquivalence_id A)

/-- 概要：Kan 標的の前合成の同値条件は合成で閉じる。
方針：逆順の前合成の式と Kan 複体間の同値の合成則を使う。
規約：始域と終域の補助模型には Kan 性は不要。
使われ方：Kerodon §4.5.1 の解像の因子分解の検査。 -/
lemma isKanPrecompositionEquivalence_comp {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsKanPrecompositionEquivalence f) (hg : IsKanPrecompositionEquivalence g) :
    IsKanPrecompositionEquivalence (f ≫ g) := by
  intro K hK
  simpa only [pre_map, NatTrans.comp_app] using (hg K).comp (hf K)

/-- 概要：単体的ホモトピーで結ばれた射は同じ Kan 標的の前合成の同値条件を持つ。
方針：前合成作用の可逆二胞体を使い、Kan な内部 Hom の同値性を移す。
規約：ホモトピーの逆向きの構成や始域の Kan 性を必要としない。
使われ方：Kerodon Proposition 4.6.7.23 の補助解像の向き付き変形。 -/
lemma isKanPrecompositionEquivalence_iff_of_homotopy {A B : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) :
    IsKanPrecompositionEquivalence f ↔ IsKanPrecompositionEquivalence g := by
  constructor
  · intro hf K hK
    exact ((hf K).isQCatEquivalence.ofFunctorIso
      (functorIsoPrecompositionOfHomotopyKan H K)).isSimplicialHomotopyEquivalence
  · intro hg K hK
    exact ((hg K).isQCatEquivalence.ofFunctorIso
      (functorIsoPrecompositionOfHomotopyKan H K).symm).isSimplicialHomotopyEquivalence

/-- 概要：隣接する二つの合成が Kan 標的の前合成の同値条件を満たせば中央の射も満たす。
方針：Kan な内部 Hom 間の二対六則を前合成の逆順に適用する。
規約：元の四つの単体集合に充填性を仮定しない。
使われ方：Kerodon §4.5.1、ホーンと面を結ぶ二つの射の同値の検出。 -/
lemma isKanPrecompositionEquivalence_of_composites {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (hfg : IsKanPrecompositionEquivalence (f ≫ g))
    (hgh : IsKanPrecompositionEquivalence (g ≫ h)) : IsKanPrecompositionEquivalence g := by
  intro K hK
  have h₀ := hfg K
  have h₁ := hgh K
  rw [pre_map, NatTrans.comp_app] at h₀ h₁
  exact isSimplicialHomotopyEquivalence_of_composites h₁ h₀

/-- 概要：ホーンの旗の最大値の自己写像は Kan 標的への前合成の同値を与える。
方針：同じホーン内の恒等射からのホモトピーと同値性のホモトピー不変性を使う。
規約：これはホーンの縮約や比較射そのものの同値性ではない。
使われ方：Kerodon Proposition 4.6.7.23 の面を通る変形の位相的な部分。 -/
lemma resolutionHornUpperMap_isKanPrecompositionEquivalence {n : ℕ} (i : Fin (n + 1)) :
    IsKanPrecompositionEquivalence (resolutionHornUpperMap.{u} i) :=
  (isKanPrecompositionEquivalence_iff_of_homotopy (resolutionHornInsertHomotopy i)).mp
    (isKanPrecompositionEquivalence_id _)

end SerrePositivity.InfinityCategories.DoldKanComparison
