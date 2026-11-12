module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedSpaceMappingSpaces

/-!
概要：Kan 複体の一点からの豊穣 Hom と元の複体の自然な同型。
方針：内部 Hom の共変作用を豊穣 whiskering と同定し、単位からの内部 Hom の自然同型を使う。
規約：対象と射を同時に比較し、反転前の係数図式の厳密な自然同型を得る。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な unstraightening 比較の係数の整理。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：Kan 複体から単体集合への忘却関手。
方針：束縛された対象の単体集合を取り、射はそのまま用いる。
規約：Kan 性を忘れるだけで宇宙は変更しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Kan 値 strict 図式の weighted nerve の係数。 -/
def kanObjectForget : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ⥤ SSet.{u} where
  obj K := K.obj
  map f := f

/-- 概要：Kan 複体の豊穣 Hom の後合成は内部 Hom 関手の射の作用に一致する。
方針：豊穣 whiskering の定義を閉モノイダル圏の curry と合成の式へ移す。
規約：始域・終域の Kan 複体は任意。
使われ方：Kerodon Construction 3.1.6.1（Tag 00TZ）、一点からの Hom の自然性の確認。 -/
lemma kanObject_sHomWhiskerLeft (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) {L M : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (f : L ⟶ M) :
    (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject).obj (Opposite.op K)).map f) =
      (ihom K.obj).map f := by
  change (ρ_ ((ihom K.obj).obj L.obj)).inv ≫
    ((ihom K.obj).obj L.obj) ◁ curry' (C := SSet.{u}) f ≫
    MonoidalClosed.comp K.obj L.obj M.obj = _
  rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]

/-- 概要：一点からの豊穣 Hom と元の Kan 複体の標準同型は全ての射について自然。
方針：標準零単体とテンソル単位の同型を内部 Hom に写し、単位の内部 Hom の自然同型を合成する。
規約：各成分は既存の pointKanObjectHomIso そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元比較の係数を元の図式へ戻す。 -/
noncomputable def pointKanObjectHomNatIso :
    (SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≅
      kanObjectForget :=
  NatIso.ofComponents _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointKanObjectHomIso (by
    intro K L f
    rw [kanObject_sHomWhiskerLeft]
    let e : (Δ[0] : SSet.{u}) ≅ 𝟙_ SSet.{u} :=
      stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit
    let θ : ihom (Δ[0] : SSet.{u}) ≅ 𝟭 SSet.{u} :=
      (internalHom (C := SSet.{u})).mapIso e.symm.op ≪≫ unitNatIso.symm
    exact θ.hom.naturality f)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
