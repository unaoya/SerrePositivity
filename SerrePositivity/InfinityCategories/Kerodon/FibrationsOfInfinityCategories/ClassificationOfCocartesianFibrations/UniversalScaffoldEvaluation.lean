module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldUnderChain
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianSectionFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianStrictTransport

/-!
概要：cocartesian strict transport の simplicial replacement を対角評価する。
方針：under の標準射列と section の族の二変数の自然性を使う。
規約：全空間への評価射の構成に射影の充填性は不要。
使われ方：一般の universal scaffold とその水平辺の計算。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories

/-- 概要：section の前合成の族の展開は始域での前合成に等しい。
方針：相対前合成の包含後の式と uncurry の自然性を使う。
規約：底上の可換性を指定した任意の射を扱う。
使われ方：対角評価における始点の変化の整合性。 -/
lemma cocartesianSectionsUncurry_overPre {T E B : SSet.{u}}
    {p : E ⟶ B} {a b : Over B} (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p b.hom) (i : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p i) =
      (i.left ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry g := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre_ι, ← Category.assoc]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_ι, ← Category.assoc, uncurry_pre_app]

/-- 概要：定値のパラメータの族の展開は、対応する section を第一射影に合成したもの。
方針：恒等の族をパラメータ頂点へ制限して回収した関手の式を使う。
規約：パラメータの単体集合 T は任意。
使われ方：水平辺の像の cocartesian 性の検証。 -/
lemma cocartesianSectionsUncurry_const {A T E B : SSet.{u}} {p : E ⟶ B} {a : A ⟶ B}
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry (SSet.const x : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) =
      fst A T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorOfVertex p a x.val := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_precomp (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a))
    (SSet.const x : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a)
  rw [Category.comp_id] at h
  rw [h]
  have he : A ◁ (SSet.const x : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p a) =
      fst A T ≫ lift (𝟙 A) (SSet.const x) := rfl
  rw [he, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_vertex]
  rfl

/-- 概要：replacement の単体を、under の標準射列に沿って全空間で評価する。
方針：under の単体と恒等パラメータの対で section の族を読む。
規約：標準単体からの射で全空間の単体を表す。
使われ方：universal scaffold の全次数の成分。 -/
def cocartesianUniversalScaffoldSimplex {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) n) :
    (Δ[n] : SSet.{u}) ⟶ E :=
  lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain s.1)) (𝟙 _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry s.2

/-- 概要：対角評価の底への射影は元の射列。
方針：section の族の射影と under の標準射列の射影を組み合わせる。
規約：射の厳密な等式。
使われ方：universal scaffold の底上の可換性。 -/
lemma cocartesianUniversalScaffoldSimplex_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) n) :
    cocartesianUniversalScaffoldSimplex p s ≫ p = SSet.yonedaEquiv.symm s.1 := by
  rw [cocartesianUniversalScaffoldSimplex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_projection,
    ← Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_yoneda_projection]

/-- 概要：対角評価は面と退化に関して自然。
方針：族の両変数の前合成と under の標準射列の制限の式を使う。
規約：単調写像の始点を固定することは要求しない。
使われ方：全空間への単体集合の射の構成。 -/
lemma cocartesianUniversalScaffoldSimplex_naturality {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {m n : SimplexCategory} (α : m ⟶ n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) n.len) :
    cocartesianUniversalScaffoldSimplex p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p) α s) =
      stdSimplex.map α ≫ cocartesianUniversalScaffoldSimplex p s := by
  rcases s with ⟨σ, τ⟩
  change lift (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) (𝟙 _) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry ((stdSimplex.map α ≫ τ) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsPre p (Over.homMk
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0))))) _ :
              Over.mk (nerveMap (Under.forget (σ.obj (α.toOrderHom 0)))) ⟶
                Over.mk (nerveMap (Under.forget (σ.obj 0))))) =
    stdSimplex.map α ≫ (lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain σ)) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry τ)
  erw [cocartesianSectionsUncurry_overPre, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry_precomp]
  simp only [← Category.assoc, lift_whiskerRight, lift_whiskerLeft,
    Category.id_comp, Category.comp_id, comp_lift]
  exact congrArg (fun f : (Δ[m.len] : SSet.{u}) ⟶ nerve (Under (σ.obj 0)) ↦
    lift f (stdSimplex.map α) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianSectionsUncurry τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_yoneda_restriction α σ).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
