module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomCartesianEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FiberwiseHomSpecialLifts

/-!
概要：cocartesian fibration の相対指数の射影は cartesian fibration。
方針：可逆化する終点指定の持ち上げを構成し、特殊辺の cartesian 判定を使う。
規約：標的 D は quasicategory、底 C には充填性を仮定しない。
使われ方：fiber ごとの普遍余錐から全空間の族を組み立てるための構造。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：始域の同型は相対的な cocartesian 辺を保存する。
方針：ホーンを同型の逆で戻し、充填を同型で再び送る。
規約：底の射は固定する。
使われ方：pullback の二つの表示での可逆化条件の照合。 -/
lemma isCocartesianEdge_map_iso {X Y B : SSet.{u}} (e : X ≅ Y) (p : Y ⟶ B)
    (s : X _⦋1⦌) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (e.hom ≫ p) s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (e.hom.app (Opposite.op ⦋1⦌) s) := by
  intro n a b ha sq
  let sq' : CommSq (a ≫ e.inv) (horn (n + 2) 0).ι (e.hom ≫ p) b :=
    ⟨by simp only [Category.assoc, e.inv_hom_id_assoc]; exact sq.w⟩
  have h : (a ≫ e.inv).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = s := by
    change e.inv.app _ (a.app _ _) = _
    rw [ha]
    exact congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) s) e.hom_inv_id
  have := hs n (a ≫ e.inv) b h sq'
  exact CommSq.HasLift.mk' {
    l := sq'.lift ≫ e.hom
    fac_left := by rw [← Category.assoc, sq'.fac_left, Category.assoc,
      e.inv_hom_id, Category.comp_id]
    fac_right := by rw [Category.assoc]; exact sq'.fac_right }

/-- 概要：終点の逆像の図式を、第一射影の cocartesian 辺を可逆にする図式へ延長できる。
方針：第二射影で構成済みの特殊持ち上げを pullback の対称同型で読み替える。
規約：底の辺と終点での図式を厳密に固定する。
使われ方：cartesian fibration の辺の存在条件。 -/
lemma exists_kanFiberwiseHom_target_extension_inverting {K C D : SSet.{u}}
    [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (b : (Δ[1] : SSet.{u}) ⟶ C)
    (H₀ : pullback ((stdSimplex.δ (0 : Fin 2)) ≫ b) p ⟶ D) :
    ∃ H : pullback b p ⟶ D,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk (stdSimplex.δ (0 : Fin 2)) rfl :
          Over.mk ((stdSimplex.δ (0 : Fin 2)) ≫ b) ⟶ Over.mk b) ≫ H = H₀ ∧
      ∀ s : (pullback b p) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b p) s →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s)) := by
  revert H₀
  rw [stdSimplex.δ_zero_eq_const]
  intro H₀
  obtain ⟨H, hH, hHi⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.exists_kanFiberwiseHom_finalVertex_extension_inverting 1 p b H₀
  refine ⟨H, hH, ?_⟩
  intro s hs
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge
      ((pullbackSymmetry b p).hom ≫ pullback.snd p b) s := by
    rw [pullbackSymmetry_hom_comp_snd]
    exact hs
  have h := hHi ((pullbackSymmetry b p).hom.app (Opposite.op ⦋1⦌) s)
    (isCocartesianEdge_map_iso (pullbackSymmetry b p) (pullback.snd p b) s hc)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (((pullbackSymmetry b p).hom ≫ (pullbackSymmetry b p).inv ≫ H).app _ s)) at h
  have hcomp : (pullbackSymmetry b p).hom ≫ (pullbackSymmetry b p).inv ≫ H = H := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hcomp] at h
  exact h

/-- 概要：cocartesian fibration の相対指数の射影は cartesian fibration。
方針：終点を固定した可逆化する図式の延長を curry し、cartesian 辺の判定を使う。
規約：D の quasicategory 性だけを要求し、C の quasicategory 性は不要。
使われ方：Kan 拡張の fiber ごとの普遍性を全空間に移す。 -/
instance fiberwiseHomProjection_cartesianFibration {K C D : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] [Quasicategory D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x b hb
    let a : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D := SSet.yonedaEquiv.symm x
    let sq : CommSq a (stdSimplex.δ (0 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) b :=
      ⟨by simpa only [a, SSet.yonedaEquiv_symm_comp] using hb.symm⟩
    let H₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p ((stdSimplex.δ (0 : Fin 2)) ≫ b)).symm
      ⟨a, sq.w⟩
    obtain ⟨H, hH, hHi⟩ := exists_kanFiberwiseHom_target_extension_inverting p b H₀
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection p b H, ?_⟩
    · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp, hH]
      exact congrArg Subtype.val
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv (D := D) p _).apply_symm_apply ⟨a, sq.w⟩)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_isCartesianEdge_of_inverting p _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomInvertingEdge_of_diagram p b H hHi)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
