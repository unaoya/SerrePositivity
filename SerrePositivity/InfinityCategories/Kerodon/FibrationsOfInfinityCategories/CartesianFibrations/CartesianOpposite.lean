module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cartesian 辺と反転した cocartesian 辺の接続。
方針：相対外側ホーンの全図式を反転し、二重反転の自然同型で戻す。
規約：底や全空間の quasicategory 性をこの移送には要求しない。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、Corollary 5.1.2.4（Tag 01TS） の双対。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cartesian 辺を反転すると cocartesian 辺。
方針：初期ホーンを反転して元の cartesian 辺で持ち上げ、解を反転する。
規約：一単体は opObjEquiv で移す。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、cartesian 辺の合成の双対化。 -/
lemma IsCartesianEdge.op {X B : SSet.{u}} {p : X ⟶ B} {e : X _⦋1⦌}
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e) := by
  intro n a b ha sq
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n a ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) b ≫ (SSet.opFunctorCompOpFunctorIso.app B).hom
  have hτ : τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) = e := by
    change (SSet.opFunctorCompOpFunctorIso.app X).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n a).app _ _) = e
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap_edge, ha]
    rfl
  have hn : SSet.opFunctor.map (SSet.opFunctor.map p) ≫
      (SSet.opFunctorCompOpFunctorIso.app B).hom =
      (SSet.opFunctorCompOpFunctorIso.app X).hom ≫ p :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality p
  have hbase : τ ≫ p = (horn (n + 2) (Fin.last (n + 2))).ι ≫ β := by
    have h := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap n z ≫
      (SSet.opFunctorCompOpFunctorIso.app B).hom) sq.w
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap] at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso_hom_ι] at h
    simpa only [τ, β, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseInitialHornMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap,
      CategoryTheory.Functor.map_comp, Category.assoc,
      hn] using h
  let hs : CommSq τ (horn (n + 2) (Fin.last (n + 2))).ι p β := ⟨hbase⟩
  have := he n τ β hτ hs
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) hs.lift
    fac_left := ?_
    fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_injective X.op (n + 2) 0
    apply (cancel_mono (SSet.opFunctorCompOpFunctorIso.app X).hom).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_double]
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso n).hom).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornReverseIndexIso_hom_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseSimplex_injective B.op (n + 2)
    apply (cancel_mono (SSet.opFunctorCompOpFunctorIso.app B).hom).1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, Category.assoc,
      hn, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_double]
    exact hs.fac_right

/-- 概要：反転した辺が cocartesian なら元の辺は cartesian。
方針：最後のホーンを最初のホーンに反転し、持ち上げを二重反転の同型で戻す。
規約：射の inner fibration 性は不要。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、cartesian 辺の合成判定への帰還。 -/
lemma isCartesianEdge_of_isCocartesianEdge_op {X B : SSet.{u}} (p : X ⟶ B)
    (e : X _⦋1⦌)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e := by
  intro n a b ha sq
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap n a
  have hτ : τ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = SSet.opObjEquiv.symm e := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap_edge, ha]
  have hbase : τ ≫ SSet.opFunctor.map p =
      (horn (n + 2) 0).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) b := by
    have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap n) sq.w
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap] at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornReverseIndexIso_hom_ι] at h
    simpa only [τ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseFinalHornMap, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap,
      CategoryTheory.Functor.map_comp, Category.assoc] using h
  let hs : CommSq τ (horn (n + 2) 0).ι (SSet.opFunctor.map p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) b) := ⟨hbase⟩
  have := he n τ _ hτ hs
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 2) hs.lift ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine CommSq.HasLift.mk' { l := F, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_injective X (n + 2) (Fin.last (n + 2))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornReverseIndexIso n).hom).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornReverseIndexIso_hom_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseSimplex_injective B (n + 2)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hs.fac_right

/-- 概要：cartesian 性は反転した辺の cocartesian 性と同値。
方針：反転した充填問題への移送と元への復元を組み合わせる。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、左右の定義の整合性。 -/
lemma isCartesianEdge_iff_isCocartesianEdge_op {X B : SSet.{u}} (p : X ⟶ B)
    (e : X _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p e ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p) (SSet.opObjEquiv.symm e) :=
  ⟨IsCartesianEdge.op, isCartesianEdge_of_isCocartesianEdge_op p e⟩

/-- 概要：三角形の最初と後半の辺が cartesian なら長辺も cartesian。
方針：三角形を反転して cocartesian 辺の合成閉性を使い、元に戻す。
規約：底を quasicategory とし、射を inner fibration とする。
使われ方：Kerodon Corollary 5.1.2.4（Tag 01TS）、cartesian な transport の合成。 -/
@[kerodon 01TS]
lemma isCartesianEdge_triangle_longEdge {X B : SSet.{u}} [Quasicategory B]
    (t : (Δ[2] : SSet.{u}) ⟶ X) (p : X ⟶ B) [InnerFibration p]
    (hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hsecond : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t)) := by
  let top : (Δ[2] : SSet.{u}) ⟶ X.op :=
    SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm (SSet.yonedaEquiv t))
  have hf (i : Fin 3) : SSet.yonedaEquiv (stdSimplex.δ i ≫ top) =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ i.rev ≫ t)) := by
    dsimp only [top]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.op_δ,
      Equiv.apply_symm_apply, ← stdSimplex.yonedaEquiv_δ_comp]
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ top)) := by
    rw [hf]
    exact hsecond.op
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (SSet.opFunctor.map p)
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ top)) := by
    rw [hf]
    exact hfirst.op
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge top (SSet.opFunctor.map p) h₀ h₁
  rw [hf] at h
  exact isCartesianEdge_of_isCocartesianEdge_op p _ h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.1.7"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge
attribute [cite HTT "2.4.2.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_iff_isCocartesianEdge_op
attribute [cite HTT "2.4.2.14" (partial := component) "仮定：底が準圏で p は CartesianFibration、後半の g は Cartesian（原典最後の文に対して Lean が強い）。結論：triangle_longEdge と triangle_first_of_second_long で f が Cartesian iff h が Cartesian を得るので「In particular」の assertion に一致。一般の local f/h と別の global lift を使う (a)(b) は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_triangle_longEdge
