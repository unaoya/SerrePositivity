module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightPrism

/-!
概要：標準単体の最初の頂点への prism による収縮。
方針：頂点 (0,j) を零に、(1,j) を j に送る単調写像を各単体に適用する。
規約：時刻一が恒等射、時刻零が最初の頂点に定値。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右ファイブレーション版。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：二点鎖と有限鎖の積を最初の頂点へ収縮する単調写像。
方針：時刻零では零、時刻一では第二成分を取る。
規約：先頭への収縮は恒等射へ向かう辺。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右側の双対な収縮。 -/
def prismFirstOrderHom (n : ℕ) : Fin 2 × Fin (n + 1) →o Fin (n + 1) where
  toFun a := if a.1 = 0 then 0 else a.2
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · rfl
    · exact Fin.zero_le _
    · have ha' : a.1.val = 1 := by have := a.1.isLt; omega
      have hb' := h.1
      simp only [hb] at hb'
      have := Fin.le_iff_val_le_val.mp hb'
      simp only [Fin.val_zero] at this
      omega
    · exact h.2

/-- 概要：標準単体の最初の頂点への収縮を単体集合の射で表す。
方針：各単体の頂点列に単調な収縮を合成する。
規約：Mathlib の cartesian tensor を用いる。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の base のホモトピー。 -/
def prismFirstContraction (n : ℕ) : (Δ[1] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[n] where
  app d := ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    ((prismFirstOrderHom n).comp
      ((stdSimplex.objEquiv s.1).toOrderHom.prod (stdSimplex.objEquiv s.2).toOrderHom)))
  naturality {d e} α := by
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨⟨e⟩⟩ := e
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：prism の指定端点の包含。
方針：第一成分を指定頂点に定値、第二成分を恒等射とする。
規約：i=0 が先頭、i=1 が終端。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） のホモトピーの制限。 -/
noncomputable def prismEndpoint (i : Fin 2) (A : SSet.{u}) : A ⟶ (Δ[1] : SSet.{u}) ⊗ A :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm i)) (𝟙 A)

/-- 概要：prism の端点の包含は単体集合の射に自然。
方針：定値成分と第二成分を次数ごとに比較する。
規約：時刻 i は固定する。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の境界の端点。 -/
lemma prismEndpoint_naturality (i : Fin 2) {A B : SSet.{u}} (f : A ⟶ B) :
    prismEndpoint i A ≫ (Δ[1] ◁ f) = f ≫ prismEndpoint i B := rfl

/-- 概要：収縮の終端は恒等射。
方針：時刻一の分岐を計算する。
規約：標準単体の全次数の等式。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の元の図式との整合。 -/
lemma prismFirstContraction_one (n : ℕ) :
    prismEndpoint 1 (Δ[n] : SSet.{u}) ≫ prismFirstContraction n = 𝟙 Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：収縮の先頭は最初の頂点に定値。
方針：時刻零の分岐を計算する。
規約：零次元の標準単体も含める。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の fiber 内の境界。 -/
lemma prismFirstContraction_zero (n : ℕ) :
    prismEndpoint 0 (Δ[n] : SSet.{u}) ≫ prismFirstContraction n =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  rfl

/-- 概要：収縮の最後の一次ホーン上の制限は第二成分の射影。
方針：ホーンの単体は零を値に取らず、収縮の時刻一の分岐に属する。
規約：Λ[1,1] を終端の端点として使う。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の境界ホモトピーの持ち上げ。 -/
lemma prismFirstContraction_horn_one (n : ℕ) :
    ((horn 1 1).ι ▷ (Δ[n] : SSet.{u})) ≫ prismFirstContraction n =
      snd (horn 1 1 : SSet.{u}) Δ[n] := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  apply stdSimplex.ext
  intro i
  have ha : a.val i ≠ 0 := by
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range a.val (1 : Fin 2)).1 a.property
    have hjval : j.val ≠ 1 := by intro h; exact hj (Fin.ext h)
    have hj0 : j = 0 := Fin.ext (by change j.val = 0; have := j.isLt; omega)
    subst j
    intro h
    exact hm ⟨i, h⟩
  exact ite_eq_right ha

/-- 概要：最後の一次ホーンの唯一の頂点。
方針：標準辺の終点は零を値に取らない。
規約：周囲の頂点番号は一。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の端点への戻し。 -/
def hornOneLastVertex : (horn 1 1 : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm 1, by
    apply (mem_horn_iff_notMem_range _ (1 : Fin 2)).2
    refine ⟨0, by decide, ?_⟩
    rintro ⟨i, hi⟩
    exact (by decide : (1 : Fin 2) ≠ 0) hi⟩

/-- 概要：prism の最後の一次ホーンの指定端点からの切断。
方針：ホーンの唯一の頂点への定値射と恒等射の組を取る。
規約：始域は任意の単体集合。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の端点の持ち上げ。 -/
noncomputable def hornOneLastSection (A : SSet.{u}) : A ⟶ (horn 1 1 : SSet.{u}) ⊗ A :=
  lift (SSet.const hornOneLastVertex) (𝟙 A)

/-- 概要：最後の一次ホーンの切断は prism の終端を選ぶ。
方針：部分型の値を取る。
規約：時刻は一。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の元の図式の回収。 -/
lemma hornOneLastSection_ι (A : SSet.{u}) :
    hornOneLastSection A ≫ ((horn 1 1).ι ▷ A) = prismEndpoint 1 A := rfl

/-- 概要：最後の一次ホーンの切断の第二成分は恒等射。
方針：組の第二射影を計算する。
規約：任意の始域。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の端点の確認。 -/
lemma hornOneLastSection_snd (A : SSet.{u}) :
    hornOneLastSection A ≫ snd (horn 1 1 : SSet.{u}) A = 𝟙 A := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
