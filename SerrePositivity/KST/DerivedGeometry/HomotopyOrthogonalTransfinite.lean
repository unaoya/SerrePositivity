module

public import SerrePositivity.KST.DerivedGeometry.NullHomotopyWellOrder

/-!
概要：後続商への直交性から連続超限列の余極限への直交性を証明する。
方針：整列帰納で互換な零ホモトピーを選び、余極限で貼り合わせる。
規約：全非輪状複体を小さい試験商で分解する存在定理はこの閉包定理の別工程。
使われ方：Stacks Lemma 19.12.3 (079L)、TT §3・§8、Toën §3.2 の非有界 K-injective 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {F : J ⥤ CochainComplex C ℤ} [F.IsWellOrderContinuous]
  (c : Cocone F) (hc : IsColimit c) (I : CochainComplex C ℤ) [∀ n, Injective (I.X n)]

include hc

/--
概要：初項と全後続商にホモトピー直交なら、連続整列列の余極限にも直交する。
方針：証明済みの整列帰納データで全段階の互換な零ホモトピーを選ぶ。
規約：極限の選択に前段階との互換性を要求し、その存在を証明する。
使われ方：Stacks 19.12.3、TT §3 の小さい試験商による判定の超限工程。
-/
lemma homotopy_orthogonal_transfinite
    (hm : ∀ (j : J) (_ : ¬IsMax j), Mono (F.map (homOfLE (Order.le_succ j))))
    (h₀ : ∀ g : F.obj ⊥ ⟶ I, Nonempty (Homotopy g 0))
    (hq : ∀ (j : J) (_ : ¬IsMax j)
      (g : cokernel (F.map (homOfLE (Order.le_succ j))) ⟶ I), Nonempty (Homotopy g 0))
    (f : c.pt ⟶ I) : Nonempty (Homotopy f 0) := by
  let d := nullHomotopyWellOrderData c f hm hq
  let s := d.sectionsMk (h₀ (c.ι.app ⊥ ≫ f)).some
  let h (a : J) : Homotopy (c.ι.app a ≫ f) 0 := s.val (op a)
  have hh {a b : J} (u : a ⟶ b) p q :
      (F.map u).f p ≫ (h b).hom p q = (h a).hom p q :=
    congrArg (fun h => h.hom p q) (s.property u.op)
  obtain ⟨k, hk⟩ := exists_colimit_compatible_homotopy c hc f h hh
  exact ⟨k⟩

end SerrePositivity.KST.DerivedGeometry
