module

public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct


/-!
# Resolution.Basic

## 概要
8 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Resolution/Basic.lean） -/

/-! # 指定された小さいK-flat dg圏解像度

## 概要
存在はこのデータ型の定義に含めない。元のdg圏のHomにK-flat性を課さない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Basic
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- dg圏の解像度版で使う、局所K-flatなdg圏と準同値の指定。 -/
structure KFlatDGResolution where
  source : Type w
  [sourceDG : DGCategory A source]
  [smallSource : Small.{u} source]
  augmentation : DGFunctor A source D
  quasiEquivalence : QuasiEquivalence augmentation
  homKFlat : localHomKFlat A source

attribute [instance] KFlatDGResolution.sourceDG KFlatDGResolution.smallSource

namespace KFlatDGResolution

/-- 既に局所K-flatな小さいdg圏は恒等準同値を解像度として使える。 -/
def refl [Small.{u} D] (hD : localHomKFlat A D) : KFlatDGResolution.{u, v, v} A D where
  source := D
  augmentation := DGFunctor.id D
  quasiEquivalence := quasiEquivalence_id
  homKFlat := hD

variable {A D}

/-- 既に与えられた準同値からの構成。準同値の存在自体は主張しない。 -/
def ofQuasiEquivalence (S : Type w) [DGCategory A S] [Small.{u} S]
    (p : DGFunctor A S D) (hp : QuasiEquivalence p) (hS : localHomKFlat A S) :
    KFlatDGResolution.{u, v, w} A D where
  source := S
  augmentation := p
  quasiEquivalence := hp
  homKFlat := hS

variable {E : Type z} [DGCategory A E]

/-- 準同値の標的を変えても同じK-flatな解像度圏を使える。 -/
def postcompose (P : KFlatDGResolution.{u, v, w} A D)
    (f : DGFunctor A D E) (hf : QuasiEquivalence f) : KFlatDGResolution.{u, z, w} A E where
  source := P.source
  augmentation := DGFunctor.comp P.augmentation f
  quasiEquivalence := quasiEquivalence_comp P.augmentation f P.quasiEquivalence hf
  homKFlat := P.homKFlat

end KFlatDGResolution
end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## CycleCover（旧 SerrePositivity/DifferentialGraded/Resolution/CycleCover.lean） -/

/-! # 全cycleを生成元とするK-flat複体被覆

## 概要
増大射はcycle上全射であり、各次数のホモロジーでも全射となる。
単射性は主張しない。dg圏の初期増大に使う。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CycleCover
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexSphereCycle_comp {K L : Complex A} (n : ℤ)
    (f : complexSphere A n ⟶ K) (g : K ⟶ L) :
    (complexSphereCycle A n (f ≫ g)).val =
      g.f n (complexSphereCycle A n f).val := rfl

/-- 任意整数次数の全cycleを添字とする。 -/
abbrev ComplexCycleIndex (K : Complex A) := Σ n : ℤ, complexCycles A K n

abbrev complexCycleCover (K : Complex A) : Complex A :=
  ∐ (fun j : ComplexCycleIndex A K => complexSphere A j.1)

def complexCycleCoverπ (K : Complex A) : complexCycleCover A K ⟶ K :=
  Sigma.desc (fun j => complexSphereMap A j.1 j.2)

lemma complexCycleCoverι_π (K : Complex A) (j : ComplexCycleIndex A K) :
    Sigma.ι (fun i : ComplexCycleIndex A K => complexSphere A i.1) j ≫
      complexCycleCoverπ A K = complexSphereMap A j.1 j.2 := Sigma.ι_comp_desc _ _

lemma complexCycleCover_kFlat (K : Complex A) : complexKFlat A (complexCycleCover A K) := by
  have : HasExactColimitsOfShape (Discrete (ComplexCycleIndex A K)) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} (ComplexCycleIndex A K)).symm)
  exact complexKFlat_colimit A
    (Discrete.functor fun j : ComplexCycleIndex A K => complexSphere A j.1)
    (fun j => complexSphere_kFlat A j.as.1)

/-- 指定cycleのsphere射を初期被覆へ持ち上げる。 -/
def complexCycleCoverLift (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    complexSphere A n ⟶ complexCycleCover A K :=
  Sigma.ι (fun j : ComplexCycleIndex A K => complexSphere A j.1) ⟨n, z⟩

lemma complexCycleCoverLift_π (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    complexCycleCoverLift A K n z ≫ complexCycleCoverπ A K = complexSphereMap A n z :=
  complexCycleCoverι_π A K ⟨n, z⟩

lemma complexCycleCover_cycle_lift (K : Complex A) (n : ℤ) (z : complexCycles A K n) :
    ∃ t : complexCycles A (complexCycleCover A K) n,
      (complexCycleCoverπ A K).f n t.val = z.val := by
  refine ⟨complexSphereCycle A n (complexCycleCoverLift A K n z), ?_⟩
  rw [← complexSphereCycle_comp, complexCycleCoverLift_π]
  exact congrArg Subtype.val ((complexSphereHomEquiv A K n).apply_symm_apply z)

/-- cycleの厳密な持ち上げからMathlibのcyclesMapの全射性を得る。 -/
lemma complexCyclesMap_epi_of_cycle_lift {K L : Complex A} (f : K ⟶ L) (n : ℤ)
    (h : ∀ z : complexCycles A L n, ∃ t : complexCycles A K n, f.f n t.val = z.val) :
    Epi (cyclesMap f n) := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro z
  have hz : L.d n (n + 1) (L.iCycles n z) = 0 := by
    exact congrArg (fun k => k z) (L.iCycles_d n (n + 1))
  obtain ⟨t, ht⟩ := h ⟨L.iCycles n z, hz⟩
  let k := moduleElementMap A (K.X n) t.val
  have hk : k ≫ K.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change K.d n (n + 1) (a • t.val) = 0
    rw [map_smul, t.property, smul_zero]
  let q := K.liftCycles k (n + 1) (by simp) hk
  refine ⟨q (1 : A), ?_⟩
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).1 inferInstance
  have hc := congrArg (fun k => k (1 : A))
    (show q ≫ cyclesMap f n ≫ L.iCycles n = k ≫ f.f n by
      rw [cyclesMap_i, ← Category.assoc, liftCycles_i])
  change L.iCycles n (cyclesMap f n (q (1 : A))) = f.f n ((1 : A) • t.val) at hc
  simpa only [one_smul] using hc.trans (by simpa only [one_smul] using ht)

lemma complexHomologyMap_epi_of_cycle_lift {K L : Complex A} (f : K ⟶ L) (n : ℤ)
    (h : ∀ z : complexCycles A L n, ∃ t : complexCycles A K n, f.f n t.val = z.val) :
    Epi (homologyMap f n) := by
  have := complexCyclesMap_epi_of_cycle_lift A f n h
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap'
    ((shortComplexFunctor (ModuleCat A) (.up ℤ) n).map f) this

lemma complexCycleCover_homology_epi (K : Complex A) (n : ℤ) :
    Epi (homologyMap (complexCycleCoverπ A K) n) :=
  complexHomologyMap_epi_of_cycle_lift A _ n (complexCycleCover_cycle_lift A K n)

end SerrePositivity.DifferentialGraded
end

end CycleCover

/-! ## CycleCoverFunctor（旧 SerrePositivity/DifferentialGraded/Resolution/CycleCoverFunctor.lean） -/

/-! # 全cycle被覆のchain mapに関する厳密な関手性

## 概要
全cycle被覆のchain mapに関する厳密な関手性。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section CycleCoverFunctor
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] {K L M : Complex A}

def complexMapCycle (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) : complexCycles A L n :=
  ⟨f.f n z.val, by
    have h := congrArg (fun g => g z.val) (f.comm n (n + 1))
    change L.d n (n + 1) (f.f n z.val) = 0
    change L.d n (n + 1) (f.f n z.val) = f.f (n + 1) (K.d n (n + 1) z.val) at h
    rw [z.property, map_zero] at h
    exact h⟩

lemma complexMapCycle_id (n : ℤ) (z : complexCycles A K n) :
    complexMapCycle A (𝟙 K) n z = z := Subtype.ext rfl

lemma complexMapCycle_comp (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) (z : complexCycles A K n) :
    complexMapCycle A (f ≫ g) n z = complexMapCycle A g n (complexMapCycle A f n z) :=
  Subtype.ext rfl

lemma complexSphereMap_mapCycle (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) :
    complexSphereMap A n z ≫ f = complexSphereMap A n (complexMapCycle A f n z) := by
  apply (complexSphereHomEquiv A L n).injective
  apply Subtype.ext
  change (complexSphereCycle A n (complexSphereMap A n z ≫ f)).val = _
  rw [complexSphereCycle_comp]
  have hz : (complexSphereCycle A n (complexSphereMap A n z)).val = z.val :=
    congrArg Subtype.val ((complexSphereHomEquiv A K n).apply_symm_apply z)
  have hf : (complexSphereCycle A n
      (complexSphereMap A n (complexMapCycle A f n z))).val = (complexMapCycle A f n z).val :=
    congrArg Subtype.val ((complexSphereHomEquiv A L n).apply_symm_apply (complexMapCycle A f n z))
  change _ = (complexSphereCycle A n (complexSphereMap A n (complexMapCycle A f n z))).val
  rw [hf]
  change f.f n (complexSphereCycle A n (complexSphereMap A n z)).val = f.f n z.val
  rw [hz]

def complexCycleCoverMap (f : K ⟶ L) : complexCycleCover A K ⟶ complexCycleCover A L :=
  Sigma.desc (fun j : ComplexCycleIndex A K =>
    complexCycleCoverLift A L j.1 (complexMapCycle A f j.1 j.2))

lemma complexCycleCoverLift_map (f : K ⟶ L) (n : ℤ) (z : complexCycles A K n) :
    complexCycleCoverLift A K n z ≫ complexCycleCoverMap A f =
      complexCycleCoverLift A L n (complexMapCycle A f n z) := Sigma.ι_comp_desc _ _

lemma complexCycleCoverMap_π (f : K ⟶ L) :
    complexCycleCoverMap A f ≫ complexCycleCoverπ A L = complexCycleCoverπ A K ≫ f := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [← Category.assoc, complexCycleCoverLift_map, complexCycleCoverLift_π,
    ← Category.assoc, complexCycleCoverLift_π, complexSphereMap_mapCycle]

lemma complexCycleCoverMap_id (K : Complex A) : complexCycleCoverMap A (𝟙 K) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [complexCycleCoverLift_map, complexMapCycle_id, Category.comp_id]

lemma complexCycleCoverMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    complexCycleCoverMap A (f ≫ g) = complexCycleCoverMap A f ≫ complexCycleCoverMap A g := by
  apply Sigma.hom_ext
  intro j
  change complexCycleCoverLift A K j.1 j.2 ≫ _ = complexCycleCoverLift A K j.1 j.2 ≫ _
  rw [complexCycleCoverLift_map, complexMapCycle_comp, ← Category.assoc,
    complexCycleCoverLift_map, complexCycleCoverLift_map]

end SerrePositivity.DifferentialGraded
end

end CycleCoverFunctor

/-! ## Initial（旧 SerrePositivity/DifferentialGraded/Resolution/Initial.lean） -/

/-! # 全Hom cycleを持ち上げる自由dg圏からの初期増大関手

## 概要
sourceの全HomはK-flat。増大関手のHomはホモロジー全射であるが、
余分なpath cycleを消すcell付加前なので準同値とはまだ主張しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section Initial
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def edges : FreeDGCategory.ComplexQuiver A D :=
  fun x y => complexCycleCover A (homObject A D x y)

abbrev Source : Type v := FreeDGCategory.Objects A D (edges A D)

/-- 対象はDと同じで、各Homのcycleを生成辺へ持ち上げる増大関手。 -/
def augmentation : DGFunctor A (Source A D) D :=
  FreeDGCategory.lift A D D (edges A D) id
    (fun x y => complexCycleCoverπ A (homObject A D x y))

lemma augmentation_obj (x : D) : (augmentation A D).obj x = x := rfl

lemma source_homKFlat : localHomKFlat A (Source A D) :=
  FreeDGCategory.homKFlat A D (edges A D)
    (fun x y => complexCycleCover_kFlat A (homObject A D x y))

lemma edge_augmentation (x y : D) :
    FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      (augmentation A D).map x y = complexCycleCoverπ A (homObject A D x y) :=
  FreeDGCategory.lift_edge A D D (edges A D) id _ x y

def sphereLift (x y : D) (n : ℤ) (z : complexCycles A (homObject A D x y) n) :
    complexSphere A n ⟶ homObject A (Source A D) x y :=
  complexCycleCoverLift A (homObject A D x y) n z ≫
    FreeDGCategory.edgeInclusion A D (edges A D) x y

lemma sphereLift_augmentation (x y : D) (n : ℤ)
    (z : complexCycles A (homObject A D x y) n) :
    sphereLift A D x y n z ≫ (augmentation A D).map x y = complexSphereMap A n z := by
  rw [sphereLift, Category.assoc, edge_augmentation]
  exact complexCycleCoverLift_π A (homObject A D x y) n z

lemma cycle_lift (x y : D) (n : ℤ) (z : complexCycles A (homObject A D x y) n) :
    ∃ t : complexCycles A (homObject A (Source A D) x y) n,
      ((augmentation A D).map x y).f n t.val = z.val := by
  refine ⟨complexSphereCycle A n (sphereLift A D x y n z), ?_⟩
  rw [← complexSphereCycle_comp, sphereLift_augmentation]
  exact congrArg Subtype.val
    ((complexSphereHomEquiv A (homObject A D x y) n).apply_symm_apply z)

lemma cyclesMap_epi (x y : D) (n : ℤ) :
    Epi (cyclesMap ((augmentation A D).map x y) n) :=
  complexCyclesMap_epi_of_cycle_lift A _ n (cycle_lift A D x y n)

lemma homologyMap_epi (x y : D) (n : ℤ) :
    Epi (homologyMap ((augmentation A D).map x y) n) :=
  complexHomologyMap_epi_of_cycle_lift A _ n (cycle_lift A D x y n)

/-- 対象写像が恒等なのでH⁰上の本質的全射性は初期段階から成り立つ。 -/
lemma augmentation_essSurj : (augmentation A D).onHomotopy.EssSurj where
  mem_essImage X := by
    let x : Source A D := ForgetEnrichment.to (C := D) (Complex A) X.as
    exact ⟨(toHomotopy A (Source A D)).obj
      (ForgetEnrichment.of (Complex A) x), ⟨Iso.refl _⟩⟩

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover
end

end Initial

/-! ## InitialComparison（旧 SerrePositivity/DifferentialGraded/Resolution/InitialComparison.lean） -/

/-! # dg関手による初期自由cycle coverの比較

## 概要
dg関手による初期自由cycle coverの比較。

## 方針
指定の共通source・準同値・局所化の比較を使い、既存の比較関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。Hom非平坦のdg圏のMorita・tensor・Hochschild型構成・K理論で、分解選択を比較する入口。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section InitialComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

def map : DGFunctor A (Source A D) (Source A E) :=
  FreeDGCategory.lift A D (Source A E) (edges A D) F.obj
    (fun x y => complexCycleCoverMap A (F.map x y) ≫
      FreeDGCategory.edgeInclusion A E (edges A E) (F.obj x) (F.obj y))

lemma map_obj (x : D) : (map A D E F).obj x = F.obj x := rfl

lemma edge_map (x y : D) :
    FreeDGCategory.edgeInclusion A D (edges A D) x y ≫ (map A D E F).map x y =
    complexCycleCoverMap A (F.map x y) ≫
      FreeDGCategory.edgeInclusion A E (edges A E) (F.obj x) (F.obj y) :=
  FreeDGCategory.lift_edge A D (Source A E) (edges A D) F.obj _ x y

lemma map_augmentation :
    (map A D E F).comp (augmentation A E) = (augmentation A D).comp F := by
  apply (FreeDGCategory.universalEquiv A D E (edges A D)).injective
  change (⟨F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    ((map A D E F).map x y ≫ (augmentation A E).map (F.obj x) (F.obj y))⟩ :
      FreeDGCategory.GeneratorMap A D E (edges A D)) =
    ⟨F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      ((augmentation A D).map x y ≫ F.map x y)⟩
  congr 1
  funext x y
  rw [← Category.assoc, edge_map, Category.assoc, edge_augmentation,
    ← Category.assoc, complexCycleCoverMap_π, edge_augmentation]

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover
end

end InitialComparison

/-! ## BoundaryCells（旧 SerrePositivity/DifferentialGraded/Resolution/BoundaryCells.lean） -/

/-! # dg圏解像度で付加する境界cellの添字と増大square

## 概要
sourceのcycleの像がtargetで境界である証人を保持する。
これはcell付加の入力であり、dg圏のpushoutや追加微分の構成ではない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundaryCells
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 次数q+1のcycleと、その増大像の次数qの原始元。 -/
structure ComplexBoundaryCell {K L : Complex A} (f : K ⟶ L) where
  degree : ℤ
  cycle : complexCycles A K (degree + 1)
  primitive : L.X degree
  boundary : L.d degree (degree + 1) primitive = f.f (degree + 1) cycle.val

namespace ComplexBoundaryCell
variable {K L : Complex A} {f : K ⟶ L} (c : ComplexBoundaryCell A f)

def attachingMap : complexSphere A (c.degree + 1) ⟶ K :=
  complexSphereMap A (c.degree + 1) c.cycle

def targetDiskMap : complexDisk A c.degree ⟶ L :=
  (complexDiskHomEquiv A L c.degree).symm c.primitive

lemma targetDiskMap_generator :
    complexDiskHomEquiv A L c.degree (c.targetDiskMap A) = c.primitive :=
  (complexDiskHomEquiv A L c.degree).apply_symm_apply c.primitive

/-- cellの境界包含と増大の可換square。新生成元の増大像は指定した原始元になる。 -/
lemma augmentation_square :
    c.attachingMap A ≫ f = complexSphereToDisk A c.degree ≫ c.targetDiskMap A := by
  apply (complexSphereHomEquiv A L (c.degree + 1)).injective
  apply Subtype.ext
  change (complexSphereCycle A (c.degree + 1) (c.attachingMap A ≫ f)).val = _
  rw [complexSphereCycle_comp]
  have hc : (complexSphereCycle A (c.degree + 1) (c.attachingMap A)).val = c.cycle.val :=
    congrArg Subtype.val ((complexSphereHomEquiv A K (c.degree + 1)).apply_symm_apply c.cycle)
  rw [hc]
  change f.f (c.degree + 1) c.cycle.val =
    (complexSphereHomEquiv A L (c.degree + 1)
      (complexSphereToDisk A c.degree ≫ c.targetDiskMap A)).val
  rw [complexSphereToDisk_comp, targetDiskMap_generator]
  exact c.boundary.symm

/-- sourceで境界を埋め、指定target原始元へ厳密に送られる条件。 -/
def HasFilling : Prop :=
  ∃ t : K.X c.degree, K.d c.degree (c.degree + 1) t = c.cycle.val ∧
    f.f c.degree t = c.primitive

/-- 全cellを埋める複体射は準同型。存在はこの条件に含めていない。 -/
lemma quasiIso_of_filling (h : ∀ c : ComplexBoundaryCell A f, c.HasFilling A) : QuasiIso f := by
  apply complex_quasiIso_of_boundary_lifting A f
  intro n z y hy
  exact h ⟨n, z, y, hy.symm⟩

end ComplexBoundaryCell

namespace DGCategoryBoundaryCells
variable (S : Type v) (D : Type w) [DGCategory A S] [DGCategory A D]

/-- 全対象対の全cycleとtarget原始元を同時に付加するための添字。 -/
abbrev Index (F : DGFunctor A S D) := Σ x : S, Σ y : S, ComplexBoundaryCell A (F.map x y)

instance indexSmall [Small.{u} S] (F : DGFunctor A S D) : Small.{u} (Index A S D F) :=
  inferInstance

end DGCategoryBoundaryCells
end SerrePositivity.DifferentialGraded
end

end BoundaryCells

/-! ## BoundarySequence（旧 SerrePositivity/DifferentialGraded/Resolution/BoundarySequence.lean） -/

/-! # 境界cellを各後続段階で埋める列の準同型判定

## 概要
dg圏のcell列が構成された後、各Homに適用する具体的な判定。
列・cell充填・余極限の存在を公理として導入しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BoundarySequence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.ComplexBoundaryCell
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]
variable (F : ℕ ⥤ Complex A) (s a : Cocone F) (hs : IsColimit s)

/-- 全有限段のcellを次段階で埋めれば、余極限でも全cellが埋まる。
transitionの次数ごとの単射性も、増大射の全射性も不要。 -/
lemma sequential_filling
    (h : ∀ (k : ℕ) (c : ComplexBoundaryCell A (a.ι.app k)),
      ∃ t : (F.obj (k + 1)).X c.degree,
        (F.obj (k + 1)).d c.degree (c.degree + 1) t =
          (F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) c.cycle.val ∧
        (a.ι.app (k + 1)).f c.degree t = c.primitive)
    (c : ComplexBoundaryCell A (hs.desc a)) : c.HasFilling A := by
  obtain ⟨k, z, hz⟩ := complexSequentialColimit_cycle_rep A F s hs (c.degree + 1) c.cycle
  have hb : a.pt.d c.degree (c.degree + 1) c.primitive =
      (a.ι.app k).f (c.degree + 1) z.val := by
    have hf := congrArg (fun f => f.f (c.degree + 1) z.val) (hs.fac a k)
    change (hs.desc a).f (c.degree + 1) ((s.ι.app k).f (c.degree + 1) z.val) =
      (a.ι.app k).f (c.degree + 1) z.val at hf
    exact c.boundary.trans ((congrArg ((hs.desc a).f (c.degree + 1)) hz.symm).trans hf)
  let ck : ComplexBoundaryCell A (a.ι.app k) := ⟨c.degree, z, c.primitive, hb⟩
  obtain ⟨t, ht, hp⟩ := h k ck
  refine ⟨(s.ι.app (k + 1)).f c.degree t, ?_, ?_⟩
  · have hd := congrArg (fun f => f t) ((s.ι.app (k + 1)).comm c.degree (c.degree + 1))
    change s.pt.d c.degree (c.degree + 1) ((s.ι.app (k + 1)).f c.degree t) =
      (s.ι.app (k + 1)).f (c.degree + 1) ((F.obj (k + 1)).d c.degree (c.degree + 1) t) at hd
    have hw := congrArg (fun f => f.f (c.degree + 1) z.val)
      (s.w (homOfLE (Nat.le_succ k)))
    change (s.ι.app (k + 1)).f (c.degree + 1)
      ((F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) z.val) =
      (s.ι.app k).f (c.degree + 1) z.val at hw
    exact hd.trans ((congrArg ((s.ι.app (k + 1)).f (c.degree + 1)) ht).trans (hw.trans hz))
  · have hf := congrArg (fun f => f.f c.degree t) (hs.fac a (k + 1))
    change (hs.desc a).f c.degree ((s.ι.app (k + 1)).f c.degree t) =
      (a.ι.app (k + 1)).f c.degree t at hf
    exact hf.trans hp

lemma sequential_quasiIso
    (h : ∀ (k : ℕ) (c : ComplexBoundaryCell A (a.ι.app k)),
      ∃ t : (F.obj (k + 1)).X c.degree,
        (F.obj (k + 1)).d c.degree (c.degree + 1) t =
          (F.map (homOfLE (Nat.le_succ k))).f (c.degree + 1) c.cycle.val ∧
        (a.ι.app (k + 1)).f c.degree t = c.primitive) : QuasiIso (hs.desc a) :=
  quasiIso_of_filling A (sequential_filling A F s a hs h)

end SerrePositivity.DifferentialGraded.ComplexBoundaryCell
end

end BoundarySequence

/-! ## CycleCoverComparisonLaws（旧 SerrePositivity/DifferentialGraded/Resolution/CycleCoverComparisonLaws.lean） -/

/-!
概要：同じ初期 cycle 被覆の比較関手の厳密恒等則・合成則。
方針：自由 dg 圏の同じ生成辺の普遍性と cycle 被覆の厳密関手性を使う。
規約：通常 dg 射の則であり、全 native Hom への作用はまだ主張しない。
使われ方：D-8 e の固定 cell 分解作用の初期段。
-/

@[expose] public section CycleCoverComparisonLaws
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma map_identity : map A D D (DGFunctor.id D) = DGFunctor.id (Source A D) := by
  apply (FreeDGCategory.universalEquiv A D (Source A D) (edges A D)).injective
  change (⟨id, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    (map A D D (DGFunctor.id D)).map x y⟩ :
      FreeDGCategory.GeneratorMap A D (Source A D) (edges A D)) =
    ⟨id, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫ 𝟙 _⟩
  congr 1
  funext x y
  rw [edge_map]
  change complexCycleCoverMap A (𝟙 _) ≫ _ = _
  rw [complexCycleCoverMap_id, Category.id_comp, Category.comp_id]
  rfl

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]

lemma map_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    map A D B (F.comp G) = (map A D E F).comp (map A E B G) := by
  apply (FreeDGCategory.universalEquiv A D (Source A B) (edges A D)).injective
  change (⟨G.obj ∘ F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    (map A D B (F.comp G)).map x y⟩ :
      FreeDGCategory.GeneratorMap A D (Source A B) (edges A D)) =
    ⟨G.obj ∘ F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      ((map A D E F).map x y ≫ (map A E B G).map (F.obj x) (F.obj y))⟩
  congr 1
  funext x y
  rw [edge_map, ← Category.assoc, edge_map, Category.assoc, edge_map]
  change complexCycleCoverMap A (F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ _ = _
  rw [complexCycleCoverMap_comp, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover
end

end CycleCoverComparisonLaws
