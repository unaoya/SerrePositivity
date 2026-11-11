module
public import SerrePositivity.KST.SConstruction.KanSpanPastingFamilies
public import SerrePositivity.KST.SConstruction.KSuspensionCompatibilityHomotopy

/-! # 元の K square の指定適合辺を保つ全貼り合わせ空間
概要：元の二三角形の復号を同じホーンへ貼り、既存の適合辺を全選択空間内で厳密に保持する。
方針：基点固定 Hom の Kan 性で選択空間の可縮性を証明し、既存の合成証人から指定頂点を作る。
規約：元の適合辺を選び直さず、指定した高次パラメータ境界の延長も提供する。
使われ方：既存 BF 適合ホモトピーと全パラメータの貼り合わせ選択を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kSuspensionSpecifiedPasting_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の square の別々の二三角形の復号を保持する全貼り合わせ空間。 -/
def kKanSuspensionPastingChoices {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) : SSet.{u} :=
  kanSpanPastingChoices
    (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f))
    (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f))

/-- 元の二三角形の全貼り合わせは、追加の Kan 仮定なしで可縮 Kan。 -/
lemma kKanSuspensionPastingChoices_isContractibleKan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kKanSuspensionPastingChoices r F f) := by
  let : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact kanSpanPastingChoices_isContractibleKan _ _

/-- 以前の指定適合辺を変更せず、同じ二三角形の全貼り合わせ空間へ入れる。 -/
def kKanSuspensionSpecifiedPastingVertex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (kKanSuspensionPastingChoices r F f) _⦋0⦌ :=
  letI : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  kanMappingSpanPastingVertex (kKanSuspensionCompatibilityComposition r F f)

/-- 元の適合辺は、指定頂点の評価で raw な一単体として厳密に回収する。 -/
lemma kKanSuspensionSpecifiedPastingVertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (kanSpanPastedEdge
      (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f))
      (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f))
      (kKanSuspensionSpecifiedPastingVertex r F f)).edge =
      (kKanSuspensionCompatibilityEdge r F f).edge := by
  let : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact congrArg SSet.Edge.edge
    (kanSpanPastedEdge_mappingSpanVertex (kKanSuspensionCompatibilityComposition r F f))

/-- 元の二三角形を保つ高次貼り合わせの選択を、指定した境界のまま延長できる。 -/
lemma kKanSuspensionPastingChoices_relative_lifting {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    {T U : SSet.{u}} (k : T ⟶ U) [Mono k] (a : T ⟶ kKanSuspensionPastingChoices r F f) :
    ∃ b : U ⟶ kKanSuspensionPastingChoices r F f, k ≫ b = a := by
  let : KanComplex (SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact kanSpanPastingChoices_relative_lifting _ _ k a

/-- 元の全貼り合わせ三角形を同時に評価する、実際の native な二単体族。 -/
def kKanSuspensionPastingFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (Δ[2] : SSet.{u}) ⊗ kKanSuspensionPastingChoices r F f ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
        ((kKanSequence (F.obj j)).level (r + 1)).space).right :=
  kanSpanPastingFamily
    (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f))
    (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f))

/-- 任意の貼り合わせの実辺を、元の固定二合成の点つき写像空間の辺として表示する。 -/
def kKanSuspensionPastingEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    (v : (kKanSuspensionPastingChoices r F f) _⦋0⦌) :
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj i)).level r).space)
      ((kKanSequence (F.obj j)).level (r + 1)).space).right.Edge
      (PointedMapping.familyVertex
        ((kKanSequence (F.obj i)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)))
      (PointedMapping.familyVertex
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
          (kKanSequence (F.obj j)).sigma r)) :=
  (kanSpanPastedEdge
    (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F f))
    (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F f)) v).ofEq
      (PointedMapping.familyVertex_eq_pointedHomVertex _).symm
      (PointedMapping.familyVertex_eq_pointedHomVertex _).symm

/-- 指定した頂点では、同じ元の点つき適合辺そのものを回収する。 -/
lemma kKanSuspensionPastingEdge_specified {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    kKanSuspensionPastingEdge r F f (kKanSuspensionSpecifiedPastingVertex r F f) =
      kKanSuspensionCompatibilityEdge r F f :=
  SSet.Edge.ext (kKanSuspensionSpecifiedPastingVertex_edge r F f)

/-- 任意の貼り合わせの選択が与える、元の構造射の実基点固定適合ホモトピー。 -/
def kKanSuspensionPastingHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    (v : (kKanSuspensionPastingChoices r F f) _⦋0⦌) :
    SSet.Homotopy
      (((kKanSequence (F.obj i)).sigma r ≫ kKanSequenceLevelMap (F.map f) (r + 1)).right)
      ((PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r).right) :=
  PointedMapping.homotopyOfEdge (kKanSuspensionPastingEdge r F f v)

/-- 指定頂点の実ホモトピーも、元の適合ホモトピーの同じ実円柱を厳密に回収する。 -/
lemma kKanSuspensionPastingHomotopy_specified {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (kKanSuspensionPastingHomotopy r F f (kKanSuspensionSpecifiedPastingVertex r F f)).h =
      (kKanSuspensionCompatibilityHomotopy r F f).h := by
  rw [kKanSuspensionPastingHomotopy, kKanSuspensionPastingEdge_specified]
  rfl

/-- 指定した境界三角形族を、実際の全パラメータの二単体族として厳密に保ち延長する。 -/
lemma kKanSuspensionPastingFamily_relative_lifting {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    {T U : SSet.{u}} (k : T ⟶ U) [Mono k] (a : T ⟶ kKanSuspensionPastingChoices r F f) :
    ∃ b : U ⟶ kKanSuspensionPastingChoices r F f, k ≫ b = a ∧
      ((Δ[2] : SSet.{u}) ◁ k) ≫ ((Δ[2] : SSet.{u}) ◁ b) ≫
        kKanSuspensionPastingFamily r F f =
      ((Δ[2] : SSet.{u}) ◁ a) ≫ kKanSuspensionPastingFamily r F f := by
  obtain ⟨b, hb⟩ := kKanSuspensionPastingChoices_relative_lifting r F f k a
  refine ⟨b, hb, ?_⟩
  rw [← whiskerLeft_comp_assoc, hb]

end SerrePositivity.KST.SConstruction
