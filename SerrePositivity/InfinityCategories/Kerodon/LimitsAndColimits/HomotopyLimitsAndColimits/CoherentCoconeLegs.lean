module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeLegs

/-!
概要：native な余錐の脚を標準区間からの実際の射とし、移送と反転の下で追跡する。
方針：指定した頂点と余錐頂点の join へ制限し、二点の標準同型で区間へ戻す。
規約：脚の比較をホモトピー類へ落とさず射の等式で扱う。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、strict な余錐の包含射の照合。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：native な余錐の指定した頂点から余錐頂点への脚の実際の単体的写像。
方針：二頂点の join への制限の後で標準区間の同型を前合成する。
規約：Kan 性も余極限性も要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、余錐の元の射との厳密な比較。 -/
def coherentCoconeLegMap {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (i : (Δ[0] : SSet.{u}) ⟶ K) : (Δ[1] : SSet.{u}) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ c.val

/-- 概要：余錐の値域の後合成は脚の後合成になる。
方針：join からの射の後合成の式を使う。
規約：値域の射 q は任意。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、反対の coherent nerve から戻す際の脚の照合。 -/
lemma coherentCoconeLegMap_post {K X Y : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (q : X ⟶ Y) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost c q) i = coherentCoconeLegMap c i ≫ q := by
  simp only [coherentCoconeLegMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconePost_val, Category.assoc]

/-- 概要：余錐の添字の制限は指定点を元の添字に写した脚となる。
方針：join の写像の合成をまとめる。
規約：添字の射 r に単射性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、元の添字へ再表示した余錐の脚。 -/
lemma coherentCoconeLegMap_restrict {K L X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (r : L ⟶ K) (i : (Δ[0] : SSet.{u}) ⟶ L) :
    coherentCoconeLegMap (c.restrict r) i = coherentCoconeLegMap c (i ≫ r) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap r (𝟙 Δ[0]) ≫ c.val) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0])), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  rfl

/-- 概要：固定図式の等式で余錐を移送しても脚は変わらない。
方針：移送した余錐の値の等式を使う。
規約：指定点は元の共通の添字の点。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、標準図式上の native な余錐の脚。 -/
lemma coherentCoconeLegMap_ofDiagramEq {K X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq h c) i = coherentCoconeLegMap c i := by
  rw [coherentCoconeLegMap, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_val]
  rfl

/-- 概要：二点の join の反転は標準区間の反転に一致する。
方針：標準同型で値域を区間に移し、二つの頂点を計算する。
規約：両方の零単体も標準反転同型で戻す。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、脚の反転の正規化。 -/
lemma pointJoinStdSimplexIso_reverse :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso.{u} 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[0]).inv =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv := by
  have hforward : SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso.{u} 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[0]).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).hom (stdSimplex.opIso ⦋0⦌).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).hom = (stdSimplex.opIso ⦋1⦌).hom := by
    apply (cancel_epi (stdSimplex.opIso ⦋1⦌).inv).1
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  let e := (SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso.{u} 0).symm) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[0] ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (stdSimplex.opIso ⦋0⦌) (stdSimplex.opIso ⦋0⦌) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0
  have he : e = stdSimplex.opIso ⦋1⦌ := Iso.ext hforward
  have h := congrArg (fun z ↦ z.inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv) he
  simpa only [e, Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, CategoryTheory.Functor.mapIso_inv,
    Iso.symm_inv, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] using h

/-- 概要：錐を反転した余錐の脚は元の脚の区間を反転した射。
方針：slice の反転の値を展開し、二点の join と標準区間の反転を計算する。
規約：元の点も標準零単体の反転同型で移す。
使われ方：HTT 4.2.4.1、通常の錐の脚から余錐の元の射への帰還。 -/
lemma coherentCoconeLegMap_reverse {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (i : (Δ[0] : SSet.{u}) ⟶ K) :
    coherentCoconeLegMap c.reverseCocone
        ((stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map i) =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) i ≫ c.val) := by
  have hval : c.reverseCocone.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso ⦋0⦌).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso (Δ[0] : SSet.{u}) K).inv ≫ SSet.opFunctor.map c.val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpObjEquiv p ⦋0⦌
      (SSet.opObjEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) _⦋0⦌ from c))).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpObjEquiv_val, Equiv.apply_symm_apply]
  have hjoin :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((stdSimplex.opIso ⦋0⦌).inv ≫ SSet.opFunctor.map i) (𝟙 Δ[0]) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K.op) (stdSimplex.opIso ⦋0⦌).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map i) (𝟙 (Δ[0] : SSet.{u}).op) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality (𝟙 (Δ[0] : SSet.{u})) i
  simp only [CategoryTheory.Functor.map_id] at hn
  unfold coherentCoconeLegMap
  rw [hval, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _), hjoin]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map i) _), hn]
  simp only [← Category.assoc]
  rw [Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.opIso ⦋0⦌).inv (stdSimplex.opIso ⦋0⦌).inv)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] Δ[0]).inv, pointJoinStdSimplexIso_reverse]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
