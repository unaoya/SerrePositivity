module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TwoStepTerminalFiber

/-!
概要：全ての右ホーンの最後の頂点を固定する二段の収縮。
方針：まず各頂点 j を max j k へ送り、次に最後の頂点へ送る。
規約：ホーン番号 k は零でない。内側ホーンにも一段の収縮を仮定しない。
使われ方：left fibration に沿う全ての右ホーンの引き戻し。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：恒等から番号 k までの押上げへの単調な prism。
方針：時刻零は j、時刻一は max j k。
規約：k はここでは任意。
使われ方：右ホーンの二段収縮の第一段。 -/
def cofinalHornRaiseOrderHom (n : ℕ) (k : Fin (n + 2)) :
    Fin 2 × Fin (n + 2) →o Fin (n + 2) where
  toFun a := if a.1 = 0 then a.2 else max a.2 k
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · exact h.2
    · exact h.2.trans (le_max_left _ _)
    · have ht := h.1
      rw [hb] at ht
      have ha' : a.1 = 0 := by
        apply Fin.ext
        have := a.1.isLt
        have := Fin.le_iff_val_le_val.mp ht
        omega
      exact (ha ha').elim
    · exact max_le_max_right k h.2

/-- 概要：番号 k までの押上げから最後の頂点への単調な prism。
方針：時刻零は max j k、時刻一は最後の頂点。
規約：k はここでは任意。
使われ方：右ホーンの二段収縮の第二段。 -/
def cofinalHornFinishOrderHom (n : ℕ) (k : Fin (n + 2)) :
    Fin 2 × Fin (n + 2) →o Fin (n + 2) where
  toFun a := if a.1 = 0 then max a.2 k else Fin.last (n + 1)
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · exact max_le_max_right k h.2
    · exact Fin.le_last _
    · have ht := h.1
      rw [hb] at ht
      have ha' : a.1 = 0 := by
        apply Fin.ext
        have := a.1.isLt
        have := Fin.le_iff_val_le_val.mp ht
        omega
      exact (ha ha').elim
    · rfl

/-- 概要：右ホーン内の最後の頂点。
方針：零が像から欠け、零はホーン番号と異なる。
規約：k ≠ 0 を要求する。
使われ方：二段の収縮の終点の指定。 -/
def cofinalRightHornVertex (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) :
    (horn (n + 1) k : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm (Fin.last (n + 1)), by
    apply (mem_horn_iff_notMem_range _ _).2
    refine ⟨0, hk.symm, ?_⟩
    rintro ⟨i, hi⟩
    change Fin.last (n + 1) = 0 at hi
    have := congrArg Fin.val hi
    simp only [Fin.val_zero, Fin.val_last] at this
    omega⟩

/-- 概要：右ホーンの恒等から押上げへの収縮。
方針：k 以外の欠けた頂点は、新たに加わる k によっては埋まらない。
規約：第一段は k = 0 でも定義できる。
使われ方：fiber を固定した最初の prism の持ち上げ。 -/
def cofinalRightHornRaise (n : ℕ) (k : Fin (n + 2)) :
    (Δ[1] : SSet.{u}) ⊗ (horn (n + 1) k : SSet.{u}) ⟶ (horn (n + 1) k : SSet.{u}) where
  app d := ↾fun s ↦ ⟨stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ((cofinalHornRaiseOrderHom n k).comp
      ((stdSimplex.objEquiv s.1).toOrderHom.prod (stdSimplex.objEquiv s.2.val).toOrderHom))), by
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range s.2.val k).1 s.2.property
    apply (mem_horn_iff_notMem_range _ _).2
    refine ⟨j, hj, ?_⟩
    rintro ⟨i, hi⟩
    change (if s.1 i = 0 then s.2.val i else max (s.2.val i) k) = j at hi
    split_ifs at hi
    · exact hm ⟨i, hi⟩
    · rcases le_total (s.2.val i) k with h | h
      · rw [max_eq_right h] at hi
        exact hj hi.symm
      · rw [max_eq_left h] at hi
        exact hm ⟨i, hi⟩⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：押上げから右ホーンの最後の頂点への収縮。
方針：出力の全頂点は k 以上なので零が欠けたまま。
規約：k ≠ 0 を要求する。
使われ方：fiber を固定した第二の prism の持ち上げ。 -/
def cofinalRightHornFinish (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) :
    (Δ[1] : SSet.{u}) ⊗ (horn (n + 1) k : SSet.{u}) ⟶ (horn (n + 1) k : SSet.{u}) where
  app d := ↾fun s ↦ ⟨stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ((cofinalHornFinishOrderHom n k).comp
      ((stdSimplex.objEquiv s.1).toOrderHom.prod (stdSimplex.objEquiv s.2.val).toOrderHom))), by
    obtain ⟨⟨d⟩⟩ := d
    apply (mem_horn_iff_notMem_range _ _).2
    refine ⟨0, hk.symm, ?_⟩
    rintro ⟨i, hi⟩
    change (if s.1 i = 0 then max (s.2.val i) k else Fin.last (n + 1)) = 0 at hi
    have hkval : k.val ≠ 0 := fun h ↦ hk (Fin.ext h)
    split_ifs at hi
    · have h := le_max_right (s.2.val i) k
      rw [hi] at h
      have := Fin.le_iff_val_le_val.mp h
      simp only [Fin.val_zero] at this
      omega
    · have := congrArg Fin.val hi
      simp only [Fin.val_zero, Fin.val_last] at this
      omega⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：第一段の先頭は恒等射。
方針：時刻零の分岐を計算する。
規約：厳密な等式。
使われ方：二段の固定した収縮の入力。 -/
lemma cofinalRightHornRaise_zero (n : ℕ) (k : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofinalRightHornRaise n k = 𝟙 _ := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：第二段の先頭は第一段の終端。
方針：両方の頂点列が max j k であることを計算する。
規約：二つの prism をこの端点で接続する。
使われ方：二段の固定した収縮の入力。 -/
lemma cofinalRightHornFinish_zero (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cofinalRightHornFinish n k hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ cofinalRightHornRaise n k := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：第二段の終端は最後の頂点に定値。
方針：時刻一の分岐を計算する。
規約：指定したホーン内の頂点への定値射。
使われ方：二段の固定した収縮の入力。 -/
lemma cofinalRightHornFinish_one (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ cofinalRightHornFinish n k hk =
      SSet.const (cofinalRightHornVertex n k hk) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：第一段は最後の頂点に定値な全ての族を固定する。
方針：max last k = last を両分岐で使う。
規約：パラメータ K は任意。
使われ方：終点 fiber の固定。 -/
lemma cofinalRightHornRaise_const (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) (K : SSet.{u}) :
    (Δ[1] ◁ (SSet.const (cofinalRightHornVertex n k hk) : K ⟶ _)) ≫
      cofinalRightHornRaise n k = SSet.const (cofinalRightHornVertex n k hk) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  change (if _ = 0 then Fin.last (n + 1) else max (Fin.last (n + 1)) k) = Fin.last (n + 1)
  rw [max_eq_left (Fin.le_last k)]
  split_ifs <;> rfl

/-- 概要：第二段も最後の頂点に定値な全ての族を固定する。
方針：時刻零と一がともに最後の頂点を取る。
規約：パラメータ K は任意。
使われ方：終点 fiber の固定。 -/
lemma cofinalRightHornFinish_const (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0) (K : SSet.{u}) :
    (Δ[1] ◁ (SSet.const (cofinalRightHornVertex n k hk) : K ⟶ _)) ≫
      cofinalRightHornFinish n k hk = SSet.const (cofinalRightHornVertex n k hk) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, s⟩
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  change (if _ = 0 then max (Fin.last (n + 1)) k else Fin.last (n + 1)) = Fin.last (n + 1)
  rw [max_eq_left (Fin.le_last k)]
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
