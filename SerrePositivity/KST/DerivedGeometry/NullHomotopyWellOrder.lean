module

public import SerrePositivity.KST.DerivedGeometry.NullHomotopyFunctor
public import SerrePositivity.KST.DerivedGeometry.CompatibleHomotopyExtension
public import SerrePositivity.KST.DerivedGeometry.CompatibleHomotopyColimit
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.Algebra.Homology.GrothendieckAbelian

/-!
概要：連続整列列に沿う零ホモトピーの互換な延長を構成する。
方針：後続段階は injective な成分延長、極限段階は余極限による貼り合わせを使う。
規約：小さい非輪状商による任意の複体の分解の存在はこの閉包補題とは別に証明する。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の試験集合による判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {J : Type w} [LinearOrder J] [SuccOrder J]
  {F : J ⥤ CochainComplex C ℤ} [F.IsWellOrderContinuous]
  (c : Cocone F) {I : CochainComplex C ℤ} (f : c.pt ⟶ I) [∀ n, Injective (I.X n)]

/--
概要：後続商への直交性から、零ホモトピーの反変関手の整列帰納データを構成する。
方針：指定した零ホモトピーを全成分で延長し、極限で互換な成分を貼り合わせる。
規約：後続射の単射性と商への直交性だけを入力する。
使われ方：Stacks 19.12.3、TT §3 の連続超限列の工程。
-/
def nullHomotopyWellOrderData
    (hm : ∀ (j : J) (_ : ¬IsMax j), Mono (F.map (homOfLE (Order.le_succ j))))
    (hq : ∀ (j : J) (_ : ¬IsMax j)
      (g : cokernel (F.map (homOfLE (Order.le_succ j))) ⟶ I), Nonempty (Homotopy g 0)) :
    (nullHomotopyFunctor c f).WellOrderInductionData := by
  apply Functor.WellOrderInductionData.ofExists
  · intro j hj h
    have := hm j hj
    let u := F.map (homOfLE (Order.le_succ j))
    let S := ShortComplex.cokernelSequence u
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact u)
        (by change Mono u; exact hm j hj) (by dsimp [S]; infer_instance)
    have hw : u ≫ (c.ι.app (Order.succ j) ≫ f) = c.ι.app j ≫ f := by
      rw [← Category.assoc, c.w]
    let h' : Homotopy (u ≫ (c.ι.app (Order.succ j) ≫ f)) 0 :=
      { hom := h.hom
        zero := h.zero
        comm i := by simpa only [hw] using h.comm i }
    obtain ⟨k, hk⟩ := exists_compatible_homotopy_extension S hS I (hq j hj)
      (c.ι.app (Order.succ j) ≫ f) h'
    refine ⟨k, ?_⟩
    change restrictNullHomotopy c f _ k = h
    ext p q
    exact hk p q
  · intro j hj s
    let c' := (Set.principalSegIio j).cocone F
    let f' := c.ι.app j ≫ f
    have hw (a : Set.Iio j) : c'.ι.app a ≫ f' = c.ι.app a.val ≫ f := by
      change F.map (homOfLE a.property.le) ≫ (c.ι.app j ≫ f) = _
      rw [← Category.assoc, c.w]
    let h' (a : Set.Iio j) : Homotopy (c'.ι.app a ≫ f') 0 :=
      { hom := (s.val (op a)).hom
        zero := (s.val (op a)).zero
        comm i := by
          have ht := (s.val (op a)).comm i
          change (c.ι.app a.val ≫ f).f i = _ at ht
          rw [hw a]
          exact ht }
    have hh {a b : Set.Iio j} (u : a ⟶ b) p q :
        (((Set.principalSegIio j).monotone.functor ⋙ F).map u).f p ≫
          (h' b).hom p q = (h' a).hom p q := by
      exact congrArg (fun h => h.hom p q) (s.property u.op)
    obtain ⟨k, hk⟩ := exists_colimit_compatible_homotopy c'
      (F.isColimitOfIsWellOrderContinuous j hj) f' h' hh
    refine ⟨k, ?_⟩
    intro i hi
    change restrictNullHomotopy c f _ k = s.val (op ⟨i, hi⟩)
    ext p q
    exact hk ⟨i, hi⟩ p q

end SerrePositivity.KST.DerivedGeometry
