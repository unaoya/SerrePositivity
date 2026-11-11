module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCollapseFibers
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：有限鎖上の全空間を区間へ写したときの両端 fiber。
方針：頂点 fiber の pullback 表示に、有限鎖の両端の pullback を貼る。
規約：全空間の射の fibration 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の比較の両端への帰着。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：部分型で定義した頂点 fiber は零単体に沿う pullback。
方針：各次数で固定条件を添え、零単体の一意性で底の成分を合わせる。
規約：底への射には頂点を指定する定値射を使う。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、Theorem 5.3.5.7（Tag 037Q）、fiber の厳密な底変換。 -/
lemma vertexFiber_isPullback {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) p
      (SSet.const b : (Δ[0] : SSet.{u}) ⟶ B) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ p = stdSimplex.isTerminalObj₀.from _ ≫ SSet.const b := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨d⟩⟩
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨congrArg (fun f ↦ f.app (Opposite.op ⦋d⦌)) hc, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.1
  · intro x y h
    refine ⟨⟨x, h⟩, rfl, ?_⟩
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have hy := (y i).isLt
    let z : (Δ[0] : SSet.{u}) _⦋d⦌ :=
      (stdSimplex.isTerminalObj₀.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).app _ ⟨x, h⟩
    change (z i).val = (y i).val
    have hz := (z i).isLt
    omega

/-- 概要：区間へ写した全空間の零 fiber は元の零頂点の fiber と同じ pullback。
方針：元の頂点 fiber の正方形に有限鎖の零 fiber の正方形を貼る。
規約：全空間の射 p は任意。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の係数の比較の値域。 -/
lemma scaffoldFiniteTotal_zero_isPullback (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin (n + 2)))))
      (stdSimplex.isTerminalObj₀.from _) (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse_zero_isPullback.{u} n
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint, SSet.yonedaEquiv_symm_zero, stdSimplex.δ_one_eq_const] at hb
  simpa only [Category.comp_id] using
    (vertexFiber_isPullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin (n + 2))))).paste_vert hb

/-- 概要：区間の零 fiber と元の零頂点の fiber の標準同型。
方針：同じ二射の pullback の一意性で比較する。
規約：順方向は元の fiber から区間の fiber へ。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、零 fiber の同値条件を元へ戻す。 -/
noncomputable def scaffoldFiniteTotalZeroFiberIso (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin (n + 2)))) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
  (scaffoldFiniteTotal_zero_isPullback n p).isoPullback ≪≫
    (vertexFiber_isPullback (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).isoPullback.symm

/-- 概要：零 fiber の同型は全空間への包含を保つ。
方針：二つの pullback の同型の第一射影の計算則を使う。
規約：全空間の射は恒等射。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、係数の fiber 比較の計算。 -/
lemma scaffoldFiniteTotalZeroFiberIso_hom_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    (scaffoldFiniteTotalZeroFiberIso n p).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (0 : Fin (n + 2)))) := by
  simp only [scaffoldFiniteTotalZeroFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

/-- 概要：尾部上の全空間は区間の一 fiber の pullback 表示。
方針：通常の底変換の正方形に有限鎖の一 fiber の正方形を貼る。
規約：尾部上の全空間は pullback p (nerveMap tail)。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の帰納仮定の値域。 -/
lemma scaffoldFiniteTotal_one_isPullback (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    IsPullback (pullback.fst p (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)))
      (stdSimplex.isTerminalObj₀.from _) (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse_one_isPullback.{u} n
  rw [stdSimplex.δ_zero_eq_const] at hb
  have hp := (IsPullback.of_hasPullback p (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n))).paste_vert hb
  convert hp using 1
  exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 概要：尾部への底変換と区間の一 fiber の標準同型。
方針：同じ pullback の二つの表示を普遍性で結ぶ。
規約：順方向は尾部上の全空間から区間の fiber へ。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、帰納仮定を区間の終点へ移す。 -/
noncomputable def scaffoldFiniteTotalOneFiberIso (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    pullback p (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  (scaffoldFiniteTotal_one_isPullback n p).isoPullback ≪≫
    (vertexFiber_isPullback (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).isoPullback.symm

/-- 概要：一 fiber の同型は全空間への第一射影を保つ。
方針：pullback の標準同型の第一射影の計算則を使う。
規約：全空間への射は尾部への底変換の第一射影。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、尾部の比較射の計算。 -/
lemma scaffoldFiniteTotalOneFiberIso_hom_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) :
    (scaffoldFiniteTotalOneFiberIso n p).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        pullback.fst p (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)) := by
  simp only [scaffoldFiniteTotalOneFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_hom_fst]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
