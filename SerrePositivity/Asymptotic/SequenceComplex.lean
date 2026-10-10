module

public import SerrePositivity.Asymptotic.FreeSequence
public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# 自由列の複体と各段の複体

各段の鎖写像・ホモトピーを列全体の鎖写像・ホモトピーに組み戻す。
射やホモトピーに有界性を要求しないため、選択した各段のデータをそのまま使える。
有界ホモトピー圏とその加法的 Karoubi 包絡も定義する。
Karoubi 包絡の三角構造やランクによる商は、この定義だけからはまだ得られない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の複体から第 `n` 段の複体を取り出す関手。 -/
def evaluateComplex (n : ℕ) :
    CochainComplex (FreeSequence R s) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)

instance (n : ℕ) : (evaluateComplex (R := R) (s := s) n).Additive :=
  inferInstanceAs ((FreeSequence.evaluation n).mapHomologicalComplex (.up ℤ)).Additive

/-- 各段の鎖写像を自由列の鎖写像に組み戻す。 -/
def assembleChainMap {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f : ∀ n, (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj Q) : P ⟶ Q where
  f i n := ((f n).f i).hom
  comm' i j _ := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((f n).comm i j)

/-- 組み戻した鎖写像の第 `n` 段は元の鎖写像である。 -/
@[simp] lemma evaluate_assembleChainMap {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f : ∀ n, (evaluateComplex n).obj P ⟶ (evaluateComplex n).obj Q) (n : ℕ) :
    (evaluateComplex n).map (assembleChainMap f) = f n := by
  ext i
  rfl

/-- 各段の鎖同型を、自由列の複体の鎖同型に組み戻す。 -/
def assembleComplexIso {P Q : CochainComplex (FreeSequence R s) ℤ}
    (e : ∀ n, (evaluateComplex n).obj P ≅ (evaluateComplex n).obj Q) : P ≅ Q where
  hom := assembleChainMap (fun n ↦ (e n).hom)
  inv := assembleChainMap (fun n ↦ (e n).inv)
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext i n
    exact congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) (e n).hom_inv_id)
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext i n
    exact congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) (e n).inv_hom_id)

/-- 各段のホモトピーを、自由列の複体間のホモトピーに組み戻す。 -/
def assembleHomotopy {P Q : CochainComplex (FreeSequence R s) ℤ} {f g : P ⟶ Q}
    (h : ∀ n, Homotopy ((evaluateComplex n).map f) ((evaluateComplex n).map g)) :
    Homotopy f g where
  hom i j n := ((h n).hom i j).hom
  zero i j hij := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((h n).zero i j hij)
  comm i := by
    funext n
    exact congrArg ModuleCat.Hom.hom ((h n).comm i)

/-- 列全体でホモトピックであることは、各段でのホモトピーの存在と同値である。 -/
lemma nonempty_homotopy_iff {P Q : CochainComplex (FreeSequence R s) ℤ} (f g : P ⟶ Q) :
    Nonempty (Homotopy f g) ↔
      ∀ n, Nonempty (Homotopy ((evaluateComplex n).map f) ((evaluateComplex n).map g)) := by
  constructor
  · rintro ⟨h⟩ n
    exact ⟨(FreeSequence.evaluation n).mapHomotopy h⟩
  · intro h
    exact ⟨assembleHomotopy (fun n ↦ Classical.choice (h n))⟩

/-- ホモトピー圏の射の等式は、各段のホモトピー圏で判定できる。 -/
lemma quotient_map_eq_iff_pointwise {P Q : CochainComplex (FreeSequence R s) ℤ}
    (f g : P ⟶ Q) :
    (HomotopyCategory.quotient _ _).map f = (HomotopyCategory.quotient _ _).map g ↔
      ∀ n, (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map f) =
        (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map g) := by
  constructor
  · intro h n
    exact HomotopyCategory.eq_of_homotopy _ _
      ((FreeSequence.evaluation n).mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h))
  · intro h
    exact HomotopyCategory.eq_of_homotopy _ _
      (assembleHomotopy (fun n ↦ HomotopyCategory.homotopyOfEq _ _ (h n)))

/-- `E_R` 上の共通有界ホモトピー圏。 -/
abbrev SequenceHomotopy (R : Type u) [CommRing R] (s : ℕ → ℕ) :=
  BoundedHomotopy (FreeSequence R s)

/-- 論文の `D_R` の加法圏としてのモデル。三角構造の延長は別の課題である。 -/
abbrev SequenceKaroubi (R : Type u) [CommRing R] (s : ℕ → ℕ) :=
  Idempotents.Karoubi (SequenceHomotopy R s)

/-- 列のホモトピー圏から、各段のホモトピー圏の積への関手。 -/
def pointwiseHomotopy : HomotopyCategory (FreeSequence R s) (.up ℤ) ⥤
    (ℕ → HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) where
  obj P n := ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).obj P
  map f n := ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map f
  map_id P := funext fun _ ↦ CategoryTheory.Functor.map_id _ P
  map_comp f g := funext fun _ ↦ CategoryTheory.Functor.map_comp _ f g

/-- ホモトピーの段ごとの組み戻しにより、積への関手は忠実である。 -/
instance : (pointwiseHomotopy (R := R) (s := s)).Faithful where
  map_injective {P Q} f g h := by
    have hf := HomotopyCategory.quotient_map_out f
    have hg := HomotopyCategory.quotient_map_out g
    rw [← hf, ← hg]
    apply (quotient_map_eq_iff_pointwise f.out g.out).2
    intro n
    change ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient _ _).map f.out) =
      ((FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map g.out)
    rw [HomotopyCategory.quotient_map_out, HomotopyCategory.quotient_map_out]
    exact congrFun h n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 各段で選んだ鎖写像を組み戻せるので、積への関手は充満である。 -/
instance : (pointwiseHomotopy (R := R) (s := s)).Full where
  map_surjective {P Q} f := by
    let g := assembleChainMap (P := P.as) (Q := Q.as) (fun n ↦ (f n).out)
    refine ⟨(HomotopyCategory.quotient _ _).map g, ?_⟩
    funext n
    change (HomotopyCategory.quotient _ _).map ((evaluateComplex n).map g) = f n
    dsimp only [g]
    rw [evaluate_assembleChainMap, HomotopyCategory.quotient_map_out]

/-- 共通有界な代表の各段には同じ次数の上下界が使える。 -/
lemma evaluateComplex_uniform_bounds (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) :
    ∃ a b : ℤ, ∀ n,
      ((evaluateComplex n).obj P).IsStrictlyGE a ∧
      ((evaluateComplex n).obj P).IsStrictlyLE b := by
  obtain ⟨a, b, ha, hb⟩ := hP
  refine ⟨a, b, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (FreeSequence.evaluation n).map_isZero (P.isZero_of_isStrictlyGE a i hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (FreeSequence.evaluation n).map_isZero (P.isZero_of_isStrictlyLE b i hi)

end SerrePositivity.Asymptotic
