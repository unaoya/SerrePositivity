module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion

/-!
# 向き付き prism の envelope

## 概要
prismatic envelope の普遍性と、自由変数の場合の完備 δ 環を定める。

## 方針
イデアルを主イデアル商で殺す射を調べ、標的の導来 p 完備性で閉包を扱う。

## 規約
標的の prism は向き付き。イデアルの完備閉包は商の完備化への核。

## 使われ方
affine Čech–Alexander 模型の各項とその射。
-/

@[expose] public section
noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：(B, J) の prismatic envelope：prism (C, dC) と δ 射 η : B → C で J ↦ dC、prism (D, dD) over (A,(d)) への J ↦ dD な
δ 射が一意に C を経由するもの（BS 著者版 Proposition 3.13 の向き付きの場合）。
方針：δ-A 代数 B は、δ 構造 DB と δ 射 ι : A → B で与える。標的の prism D は有界性を要求しない。
規約：C の prism のイデアルは (d)C（`ideal_eq`）。η ∘ ι は prism の射（`base_hom`）。
使われ方：Constr 4.17 の C、Ex 7.9、Thm 5.2 の pd 包との比較。 -/
structure IsPrismaticEnvelope
    {B : Type u} [CommRing B] (DB : DeltaStructure p B) (ι : A →+* B)
    (hι : P.deltaStructure.IsDeltaHom DB ι) (J : Ideal B) (hJ : ι P.generator ∈ J)
    {C : Type u} [CommRing C] (Q : OrientedPrism p C) (η : B →+* C) : Prop where
  /-- η は δ 射。 -/
  isDeltaHom : DB.IsDeltaHom Q.deltaStructure η
  /-- (A,(d)) → (C, dC) は prism の射（η ∘ ι）。 -/
  base_hom : P.ideal ≤ Q.ideal.comap (η.comp ι)
  /-- C のイデアルは d の像で生成される（剛性の帰結でもある）。 -/
  ideal_eq : Q.ideal = Ideal.span {η (ι P.generator)}
  /-- J は dC に入る。 -/
  map_le : J.map η ≤ Q.ideal
  /-- 普遍性：任意の prism (D, dD) over (A,(d)) と、J ↦ dD な δ-A 射 g : B → D は一意に η を経由する。 -/
  lift : ∀ {D : Type u} [CommRing D] (QD : OrientedPrism p D) (g : B →+* D),
    DB.IsDeltaHom QD.deltaStructure g → P.ideal ≤ QD.ideal.comap (g.comp ι) → J.map g ≤ QD.ideal →
      ∃! h : C →+* D, Q.deltaStructure.IsDeltaHom QD.deltaStructure h ∧ h.comp η = g

/-- 概要：envelope は同型を除いて一意（BS 著者版 Proposition 3.13 の普遍性の帰結）。
方針：二つの envelope の間の lift の合成が恒等。
規約：環同型で、δ 射。
使われ方：Constr 4.17 の対象の選択によらないこと。 -/
theorem IsPrismaticEnvelope.unique
    {B : Type u} [CommRing B] {DB : DeltaStructure p B} {ι : A →+* B}
    {hι : P.deltaStructure.IsDeltaHom DB ι} {J : Ideal B} {hJ : ι P.generator ∈ J}
    {C C' : Type u} [CommRing C] [CommRing C'] {Q : OrientedPrism p C} {Q' : OrientedPrism p C'}
    {η : B →+* C} {η' : B →+* C'}
    (h : IsPrismaticEnvelope P DB ι hι J hJ Q η) (h' : IsPrismaticEnvelope P DB ι hι J hJ Q' η') :
    ∃ e : C ≃+* C', Q.deltaStructure.IsDeltaHom Q'.deltaStructure e.toRingHom ∧ e.toRingHom.comp η = η' := by
  obtain ⟨f, hf, _⟩ := h.lift Q' η' h'.isDeltaHom h'.base_hom h'.map_le
  obtain ⟨g, hg, _⟩ := h'.lift Q η h.isDeltaHom h.base_hom h.map_le
  obtain ⟨a, _, hau⟩ := h.lift Q η h.isDeltaHom h.base_hom h.map_le
  obtain ⟨b, _, hbu⟩ := h'.lift Q' η' h'.isDeltaHom h'.base_hom h'.map_le
  have hgf : g.comp f = RingHom.id C := by
    apply (hau (g.comp f) ⟨hg.1.comp hf.1, ?_⟩).trans
      (hau (RingHom.id C) ⟨Q.deltaStructure.isDeltaHom_id, RingHom.id_comp η⟩).symm
    rw [RingHom.comp_assoc, hf.2, hg.2]
  have hfg : f.comp g = RingHom.id C' := by
    apply (hbu (f.comp g) ⟨hf.1.comp hg.1, ?_⟩).trans
      (hbu (RingHom.id C') ⟨Q'.deltaStructure.isDeltaHom_id, RingHom.id_comp η'⟩).symm
    rw [RingHom.comp_assoc, hg.2, hf.2]
  exact ⟨RingEquiv.ofRingHom f g hfg hgf, hf.1, hf.2⟩

/-- J₀ を殺した後の一変数導来 p 完備化への標準射の核。 -/
def envelopeClosure {B : Type u} [CommRing B] (p : ℕ) (J₀ : Ideal B) : Ideal B := by
  let T := B ⧸ J₀
  letI := principalCompletionCommRing T (p : T)
  exact RingHom.ker ((principalCompletionUnitRingHom T (p : T)).comp (Ideal.Quotient.mk J₀))

/-- 元のイデアルは完備化へ送ったときの核に含まれる。 -/
theorem le_envelopeClosure {B : Type u} [CommRing B] (p : ℕ) (J₀ : Ideal B) :
    J₀ ≤ envelopeClosure p J₀ := by
  intro x hx
  change principalCompletionUnitRingHom (B ⧸ J₀) (p : B ⧸ J₀) (Ideal.Quotient.mk J₀ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem envelopeClosure_map_le {B D : Type u} [CommRing B] [CommRing D]
    (J₀ : Ideal B) (QD : OrientedPrism p D) (g : B →+* D)
    (hg : J₀.map g ≤ QD.ideal) :
    (envelopeClosure p J₀).map g ≤ QD.ideal := by
  let T := B ⧸ J₀
  let U := D ⧸ QD.ideal
  let q := Ideal.Quotient.mk QD.ideal
  let f : T →+* U := Ideal.Quotient.lift J₀ (q.comp g)
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hg (Ideal.mem_map_of_mem _ hx)))
  let := f.toAlgebra
  have hU : IsModuleComplete U (p : U) (ModuleCat.of U U) :=
    isModuleComplete_principal_quotient_natCast D p QD.generator QD.complete_p
  have hc : IsModuleComplete T (p : T) (ModuleCat.of T U) := by
    apply (isModuleComplete_algebraMap_iff T U (p : T) U).mp
    change IsModuleComplete U (f (p : T)) (ModuleCat.of U U)
    rw [map_natCast]
    exact hU
  have hl := principalCompletionLift_comp T (p : T) U f hc
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change g x ∈ QD.ideal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (Ideal.Quotient.mk J₀ x) = 0
  have hx' : principalCompletionUnitRingHom T (p : T) (Ideal.Quotient.mk J₀ x) = 0 := hx
  rw [← RingHom.congr_fun hl, RingHom.comp_apply, hx', map_zero]

/-- 概要：J を完備閉包で置き換えても envelope は同じ
（BS 著者版 Construction 4.17 のイデアルと閉包の比較）。
方針：標的 D は (p,d) 完備なので、J₀B ↦ dD なら閉包も ↦ dD。
規約：閉包は導来 p 完備化の H⁰ への核で述べる。
使われ方：Constr 4.17 の J の形を原典どおりにしたまま、変数の場合の存在定理を当てる。 -/
theorem IsPrismaticEnvelope.of_closure {B : Type u} [CommRing B]
    (DB : DeltaStructure p B) (ι : A →+* B) (hι : P.deltaStructure.IsDeltaHom DB ι)
    (J₀ : Ideal B) (h₀ : ι P.generator ∈ J₀)
    {C : Type u} [CommRing C] (Q : OrientedPrism p C) (η : B →+* C) :
    IsPrismaticEnvelope P DB ι hι J₀ h₀ Q η ↔
      IsPrismaticEnvelope P DB ι hι (envelopeClosure p J₀) (le_envelopeClosure p J₀ h₀) Q η := by
  have htest {D : Type u} [CommRing D] (QD : OrientedPrism p D) (g : B →+* D) :
      J₀.map g ≤ QD.ideal ↔ (envelopeClosure p J₀).map g ≤ QD.ideal :=
    ⟨envelopeClosure_map_le J₀ QD g, fun h =>
      (Ideal.map_mono (le_envelopeClosure p J₀)).trans h⟩
  constructor
  · intro h
    exact ⟨h.isDeltaHom, h.base_hom, h.ideal_eq, (htest Q η).mp h.map_le,
      fun QD g hd hb hm => h.lift QD g hd hb ((htest QD g).mpr hm)⟩
  · intro h
    exact ⟨h.isDeltaHom, h.base_hom, h.ideal_eq, (htest Q η).mpr h.map_le,
      fun QD g hd hb hm => h.lift QD g hd hb ((htest QD g).mp hm)⟩

/-! ## 存在：変数の場合（Ex 3.14） -/

/-- 概要：集合 S 上の完備化した自由 δ-A 代数 A{X_S}^∧ := (RelativeFreeDeltaRing S)^∧（導来 (p,d) 完備化の H⁰）。
方針：既存の `RelativeFreeDeltaRing`（= MvPolynomial (S × ℕ) A）と `PDCompletionH0`、δ 構造は `deltaPDCompletionStructure`。
規約：原典の Free_{δ,A}(B₀)^∧（B₀ = A⟨X_S⟩）と同じ（自由 δ 代数と多項式代数の左随伴の合成。一致は別の補題）。
使われ方：Constr 4.17 の B、変数の場合の envelope の模型。 -/
abbrev completedFreeDelta (S : Type u) : Type u :=
  PDCompletionH0 (RelativeFreeDeltaRing (R := A) S) p (algebraMap A _ P.generator)

instance (S : Type u) : CommRing (completedFreeDelta P S) :=
  pdCompletionCommRing _ p _

/-- 概要：完備化した自由 δ 環の δ 構造。
方針：`deltaPDCompletionStructure`。
規約：`relativeFreeDeltaStructure S P.deltaStructure` を完備化へ延ばす。
使われ方：envelope の始域。 -/
def completedFreeDeltaStructure (S : Type u) : DeltaStructure p (completedFreeDelta P S) :=
  deltaPDCompletionStructure (relativeFreeDeltaStructure S P.deltaStructure) (algebraMap A _ P.generator)

/-- 概要：A → A{X_S}^∧ は δ 射。
方針：定数の包含と完備化の単位の合成。
規約：—
使われ方：`IsPrismaticEnvelope` の ι。 -/
def completedFreeDeltaBase (S : Type u) : A →+* completedFreeDelta P S :=
  (pdCompletionUnit _ p _).comp (algebraMap A (RelativeFreeDeltaRing (R := A) S))

/-- 定数の包含と完備化の合成は δ 構造を保つ。 -/
theorem completedFreeDeltaBase_isDeltaHom (S : Type u) :
    P.deltaStructure.IsDeltaHom (completedFreeDeltaStructure P S) (completedFreeDeltaBase P S) := by
  exact (pdCompletionUnit_isDeltaHom (relativeFreeDeltaStructure S P.deltaStructure)
    (algebraMap A _ P.generator)).comp (relativeFreeDeltaStructure_C_isDeltaHom S P.deltaStructure)

/-- 概要：変数の部分集合 Z ⊆ S と d で生成されるイデアル (d, X_z : z ∈ Z)。
方針：生成元の像の span。
規約：Ex 3.14 の状況を変数変換した後の形。
使われ方：存在定理の J。 -/
def variableIdeal (S : Type u) (Z : Set S) : Ideal (completedFreeDelta P S) :=
  Ideal.span (insert (completedFreeDeltaBase P S P.generator) (Set.range (fun z : Z =>
    pdCompletionUnit (RelativeFreeDeltaRing (R := A) S) p (algebraMap A _ P.generator)
      (MvPolynomial.X ((z : S), 0)))))


end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Ex 3.14" (partial := special) "自由変数（候補環の生成元が正則）の envelope。一般の滑らかな B₀ → R は未 ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.of_closure
attribute [cite BS19 "Prop 3.13" (partial := special) "向き付き・B＝完備自由 δ 環・J＝(d, 変数) の場合に存在と完全平坦性 (1)。底変換 (2) は変数の場合が本体（prismaticEnvelope_completedBaseChange_of_variables）。一般の正則な B, J は未 ／ 11-10 更新 ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope
attribute [cite BS19 "Prop 3.13" (partial := special) "向き付き・B＝完備自由 δ 環・J＝(d, 変数) の場合に存在と完全平坦性 (1)。底変換 (2) は変数の場合が本体（prismaticEnvelope_completedBaseChange_of_variables）。一般の正則な B, J は未 ／ 11-10 更新 ／ 11-12 夜更新（ノート本文の更新時）"] _root_.SerrePositivity.BhattScholze.Prismatic.IsPrismaticEnvelope.unique
