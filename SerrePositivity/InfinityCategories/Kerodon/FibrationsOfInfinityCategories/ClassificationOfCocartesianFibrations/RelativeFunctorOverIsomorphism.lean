module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：底上の全空間の同型による相対写像空間の厳密な移送。
方針：後合成を通常の関手にし、前合成と合わせて同型を写す。
規約：底を固定し、充填性や同値の逆射の選択は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい unstraightening の写像空間との比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：定義域の底への射を固定した相対関手空間は標的の共変関手。
方針：底上の射を後合成に写し、その単位と合成の計算則を使う。
規約：定義域と標的の quasicategory 性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、相対写像空間の標的の同型の移送。 -/
def relativeFunctorOverPostFunctor {A B : SSet.{u}} (a : A ⟶ B) : Over B ⥤ SSet.{u} where
  obj p := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a
  map {p q} f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p.hom q.hom f.left f.w a
  map_id p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_id p.hom a
  map_comp {p q r} f g :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_comp p.hom q.hom r.hom f.left f.w g.left g.w a).symm

/-- 概要：底上の始域と標的の同型は相対写像空間の厳密な同型を誘導する。
方針：始域の逆向きの同型の前合成と、標的の同型の後合成を続ける。
規約：始域の同型は a から a'、標的の同型は p から p'。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、縮小同型による相対写像空間の同定。 -/
noncomputable def relativeFunctorOverIso {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p.hom a.hom ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p'.hom a'.hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverFunctor p.hom).mapIso ea.symm.op ≪≫
    (relativeFunctorOverPostFunctor a'.hom).mapIso ep

/-- 概要：全空間の同型による写像空間の順方向は逆向きの前合成と順方向の後合成。
方針：関手が同型に作用する定義を展開する。
規約：底上の同型の実際の射を保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、縮小した写像空間の評価の計算。 -/
lemma relativeFunctorOverIso_hom {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p') :
    (relativeFunctorOverIso ea ep).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.hom ea.inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p.hom p'.hom ep.hom.left ep.hom.w a'.hom := rfl

/-- 概要：写像空間の同型の順方向は底上の射を二つの全空間の同型で共役する。
方針：相対前合成と後合成の頂点の公式を続けて使う。
規約：始域側は同型の逆、標的側は同型の順方向を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、小さい写像空間と元の比較射の整合性。 -/
lemma relativeFunctorOverIso_vertex {B : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p')
    (f : a.left ⟶ p.left) (hf : f ≫ p.hom = a.hom) :
    (relativeFunctorOverIso ea ep).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p.hom a.hom f hf) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p'.hom a'.hom ((ea.inv.left ≫ f) ≫ ep.hom.left)
        (by rw [Category.assoc, ep.hom.w, Category.assoc, hf, ea.inv.w]) := by
  rw [relativeFunctorOverIso_hom]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost p.hom p'.hom ep.hom.left ep.hom.w a'.hom).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre p.hom ea.inv).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p.hom a.hom f hf)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_vertex]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
