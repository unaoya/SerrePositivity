module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：アフィン遷移射を持つ逆系で、固有射の全射性を有限段に降ろす。
方針：固有射の閉像の補開集合を取り、その逆像が極限で空なら有限段ですでに空と示す。
規約：近似モデルの固有射は入力とする。像の補開集合の準コンパクト性だけを使う。
使われ方：BS17 Lemma 2.6 における Noether 近似後の全射性。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクト開の極限への逆像が空なら、その逆像はある有限段で空。
方針：すべての段で非空なら、制限した逆系の極限も非空になる。
規約：遷移射はアフィン。基底全体の準コンパクト性は仮定しない。
使われ方：固有射の閉像の補開集合が消える段を選ぶ。
-/
theorem exists_preimage_eq_bot_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    {c : Cone D} (hc : IsLimit c) {i : I} (U : (D.obj i).Opens)
    (hU : IsCompact U.carrier) (hempty : c.π.app i ⁻¹ᵁ U = ⊥) :
    ∃ (j : I) (a : j ⟶ i), D.map a ⁻¹ᵁ U = ⊥ := by
  by_contra! h
  let F := opensDiagram D i U
  have (j : Over i) : CompactSpace (F.obj j) :=
    isCompact_iff_compactSpace.mp ((D.map j.hom).isCompact_preimage hU)
  have (j : Over i) : Nonempty (F.obj j) := by
    change Nonempty (D.map j.hom ⁻¹ᵁ U).toScheme
    exact Set.nonempty_coe_sort.mpr
      (Set.nonempty_iff_ne_empty.mpr (SetLike.coe_injective.ne (h j.left j.hom)))
  have : Nonempty (c.π.app i ⁻¹ᵁ U).toScheme :=
    Scheme.nonempty_of_isLimit F (opensCone D c i U) (isLimitOpensCone D c hc i U)
  rw [hempty] at this
  exact this.elim fun x => x.property

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether な段にある固有射が極限上で全射なら、ある有限段への引き戻しが全射。
方針：引き戻しの点集合の像は、元の射の像の逆像に等しい。
規約：固有射のモデルは既に与えられているとする。
使われ方：有限表示の固有全射を Noether モデルで扱う際の全射性の降下。
-/
theorem exists_surjective_pullback_snd_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    {c : Cone D} (hc : IsLimit c) {i : I} [_root_.AlgebraicGeometry.IsNoetherian (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [IsProper f]
    [Surjective (pullback.snd f (c.π.app i))] :
    ∃ (j : I) (a : j ⟶ i), Surjective (pullback.snd f (D.map a)) := by
  let U : (D.obj i).Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hempty : c.π.app i ⁻¹ᵁ U = ⊥ := by
    ext x
    change (c.π.app i x ∉ Set.range f) ↔ False
    rw [← Set.mem_preimage, ← Scheme.Pullback.range_snd, Set.range_eq_univ.mpr
      (pullback.snd f (c.π.app i)).surjective]
    simp
  obtain ⟨j, a, ha⟩ := exists_preimage_eq_bot_of_isLimit D hc U
    (TopologicalSpace.NoetherianSpace.isCompact _) hempty
  refine ⟨j, a, ⟨?_⟩⟩
  rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, ← Set.compl_empty_iff]
  exact congrArg (fun V : (D.obj j).Opens => V.carrier) ha

end SerrePositivity.AlgebraicGeometry
