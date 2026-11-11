module
public import SerrePositivity.KST.SConstruction.ObjectSHomotopy
public import SerrePositivity.KST.SConstruction.STwoCofiberModel
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # object S による自明ファイブレーションの弱同値への移送
概要：安定な入力間の trivial Kan fibration は object S の単体ホモトピー同値を誘導する。
方針：切断の完全性を制限で反映し、二つの関手同型を object S の実ホモトピーに送る。
規約：object/core 比較の弱同値性を仮定しない。使われ方：Fiore–Pieper Proposition 4.27 と模型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- 概要：自明ファイブレーションの厳密な切断は零対象と全押し出しを保つ。
方針：射影の普遍性の反映と切断の式を使う。
規約：両端は quasicategory、安定性は不要。使われ方：object S の完全なホモトピー逆。 -/
lemma preservesSConstructionData_section_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 _) : PreservesSConstructionData s := by
  constructor
  · intro z hz
    apply (isZeroVertex_iff_of_trivialKanFibration p _).2
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) z
    change p.app (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) z) = z at he
    rw [he]
    exact hz
  · intro F hF
    apply (isPushoutSquare_iff_postcomp_of_trivialKanFibration p _).2
    rw [Category.assoc, hs, Category.comp_id]
    exact hF

/-- 概要：完全な逆と二つの関手同型を持つ射は object S の単体ホモトピー同値を誘導する。
方針：二つの関手同型を実際の単体ホモトピーへ送り、object S の関手法則で両端を照合する。
規約：逆は安定な入力間の射。使われ方：自明ファイブレーションの逆の利用。 -/
lemma objectS_map_isSimplicialHomotopyEquivalence_of_inverse {X Y : StableModel.{u}}
    (p : X ⟶ Y) (s : Y ⟶ X) (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p.val ≫ s.val) (𝟙 X.carrier))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (s.val ≫ p.val) (𝟙 Y.carrier)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (objectSConstructionFunctor.map p) := by
  refine ⟨objectSConstructionFunctor.map s, ?_, ?_⟩
  · have H := objectSHomotopyOfFunctorIso (f := p ≫ s) (g := 𝟙 X) h₀
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (show Nonempty (SSet.Homotopy (objectSConstructionFunctor.map (p ≫ s))
        (objectSConstructionFunctor.map (𝟙 X))) from ⟨H⟩)
  · have H := objectSHomotopyOfFunctorIso (f := s ≫ p) (g := 𝟙 Y) h₁
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      (show Nonempty (SSet.Homotopy (objectSConstructionFunctor.map (s ≫ p))
        (objectSConstructionFunctor.map (𝟙 Y))) from ⟨H⟩)

/-- 概要：自明ファイブレーションは object S の実際の単体ホモトピー同値を誘導する。
方針：完全な切断と同じ基底上の二つの関手同型を実際に構成する。
規約：逆や同型の存在を追加仮定にしない。使われ方：object S の模型の弱同値比較。 -/
lemma objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
    {X Y : StableModel.{u}} (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (objectSConstructionFunctor.map p) := by
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section p.val
  have hs' := (preservesSConstructionData_section_of_trivialKanFibration p.val s hs).toCofiberData
  let s' : Y ⟶ X := ⟨s, hs'⟩
  apply objectS_map_isSimplicialHomotopyEquivalence_of_inverse p s'
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration p.val _ _ (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (𝟙 Y.carrier) _ _ (by
      rw [Category.comp_id, Category.id_comp]
      exact hs)

/-- 概要：自明ファイブレーションの object S の像は anodyne 局所化で同型。
方針：構成した二つの実ホモトピーを局所化で等号に送り、像の逆を作る。
規約：object S 自身の Kan 性は要求しない。使われ方：McCarthy の object 単体集合での模型比較。 -/
lemma objectS_map_localized_isIso_of_trivialKanFibration {X Y : StableModel.{u}}
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSConstructionFunctor.map p)) := by
  obtain ⟨s, ⟨H₀⟩, ⟨H₁⟩⟩ := objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration p
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  exact ⟨⟨Q.map s,
    (Q.map_comp _ _).symm.trans ((AnodyneHomotopy.map_homotopy_eq Q hQ H₀).trans (Q.map_id _)),
    (Q.map_comp _ _).symm.trans ((AnodyneHomotopy.map_homotopy_eq Q hQ H₁).trans (Q.map_id _))⟩⟩

/-- 概要：S₂ と全 cofiber 正方形の比較は object S の後も弱同値。
方針：中央制限の実際の自明ファイブレーションに object S の保存定理を適用する。
規約：object/core 比較や加法性を仮定しない。使われ方：McCarthy の正方形表示への移送。 -/
lemma sTwoCofiberComparison_objectS_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectSConstructionFunctor.map (sTwoCofiberComparison X))) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sTwoCofiberComparison X).val :=
    sTwoCofiberRestriction_trivialKanFibration X.carrier
  exact objectS_map_localized_isIso_of_trivialKanFibration (sTwoCofiberComparison X)

end SerrePositivity.KST.SConstruction
