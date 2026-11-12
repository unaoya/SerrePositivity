module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanCoproducts
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanCoconeColimits

/-!
概要：Kan 複体の実際の小さい余積を空間の ∞ 圏 𝒮 の余極限余錐として公開する。
方針：次数ごとの直和の Kan 性と台の余積の普遍性を検証し、全反変 Hom を介して移送する。
規約：F1 の既存の図式 kanDiagramCoherentNerve F 上に余錐を置く。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、F2 が使う空余積を含む小さい余積。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {J : Type u}

/-- 概要：Kan 複体の任意の小さい族の直和を Kan な対象に束縛する。
方針：次数ごとの直和とその直接の Kan 充填を使う。
規約：J に有限性・非空性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の実際の余積対象。 -/
def kanCoproductObject (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct (fun j : J ↦ (F.obj ⟨j⟩).obj), inferInstance⟩

/-- 概要：Kan 複体の族の直和への標準包含からなる通常の余錐。
方針：各単体に成分添字を付ける包含を離散図式の自然変換とする。
規約：頂点は kanCoproductObject F そのもの。
使われ方：HTT 4.2.4.1、𝒮 の余積の strict な入力余錐。 -/
def kanCoproductCocone (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : Cocone F where
  pt := kanCoproductObject F
  ι := Discrete.natTrans (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductι (fun k : J ↦ (F.obj ⟨k⟩).obj) j.as)

/-- 概要：Kan 複体の直和の余錐の台は単体集合の余極限余錐。
方針：直和からの降下射と成分ごとの射の外延性を使う。
規約：任意の小さい族を元の図式の表示のまま扱う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、反変 Hom の極限条件の検証。 -/
def kanCoproductCocone_forget_isColimit (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone (kanCoproductCocone F)) where
  desc s := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductDesc (fun j : J ↦ (F.obj ⟨j⟩).obj) (fun j ↦ s.ι.app ⟨j⟩)
  fac _ _ := rfl
  uniq s m hm := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproduct_hom_ext _ (fun j ↦ by
    exact (hm ⟨j⟩).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialCoproductι_desc _ (fun j ↦ s.ι.app ⟨j⟩) j).symm)

/-- 概要：束縛した直和は通常の Kan 複体の圏でも余積。
方針：台の余極限性を忘却関手による判定で戻す。
規約：Hom の同値類でなく実際の射の普遍性。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の小さい余積の通常の圏の普遍性。 -/
noncomputable def kanCoproductCocone_isColimit (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsColimit (kanCoproductCocone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCocone_isColimit_of_forget _ (kanCoproductCocone_forget_isColimit F)

/-- 概要：空間の ∞ 圏の既存の図式上の実際の余積余錐。
方針：通常の直和の余錐を coherent nerve へ移し、既存の図式への等式で移送する。
規約：頂点は置換せず kanCoproductObject F を使う。
使われ方：HTT 4.2.4.1、F2 が使う 𝒮 の小さい余積余錐。 -/
noncomputable def spaceCoproductCocone (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanCoproductCocone F))

/-- 概要：空間の余積余錐の頂点は実際の直和の標準頂点。
方針：図式の等式での移送と strict な余錐は元の頂点を保持する。
規約：同値でなく頂点の厳密な等号。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の余積対象の同定。 -/
lemma spaceCoproductCocone_vertex (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceCoproductCocone F).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (kanCoproductObject F) := by
  rw [spaceCoproductCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：実際の Kan 複体の直和の余錐は空間の ∞ 圏の余極限余錐。
方針：台の普遍性から全反変 Hom の極限性を検証し、native な余極限判定へ移す。
規約：J は任意で空余積を含む。比較同値や Hom 条件を追加の仮定にしない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、F2 の 𝒮 の小さい余積。 -/
lemma spaceCoproductCocone_isColimitCone (F : Discrete J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (spaceCoproductCocone F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanCoproductCocone F))).mp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCocone_isColimit_of_kanDiscrete_forget _
    (kanCoproductCocone_forget_isColimit F)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
