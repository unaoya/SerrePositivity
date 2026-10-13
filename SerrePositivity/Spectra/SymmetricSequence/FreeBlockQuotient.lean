module

public import SerrePositivity.Spectra.SymmetricSequence.FreeInduction
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # 自由convolutionの各段のブロック作用による商表示

第一ブロックをm−nに固定し、全単射で添字付けた余積を対称群の関係式で割る。
二つの射の余等化子の普遍性から、自由convolutionの各段との比較同型を構成する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- 第一ブロックm−nと第二ブロックnから出力mへの全単射。 -/
abbrev FreeBlockIndex (n m : ℕ) :=
  FiniteBijection.sumObj (FiniteBijection.of (m - n)) (FiniteBijection.of n) ⟶
    FiniteBijection.of m

/-- n以上の段では、全単射の添字は出力の対称群と同値。 -/
def freeBlockIndexEquivPerm (n m : ℕ) (hm : n ≤ m) :
    FreeBlockIndex n m ≃ Equiv.Perm (Fin m) := by
  have h : m - n + n = m := Nat.sub_add_cancel hm
  have ho : FiniteBijection.sumObj (FiniteBijection.of (m - n)) (FiniteBijection.of n) =
      FiniteBijection.of m := congrArg FiniteBijection.of h
  unfold FreeBlockIndex
  rw [ho]
  exact FiniteBijection.homEquiv _ _

/-- 全単射で添字付けた、固定次数のテンソル積の余積。 -/
def freeBlockGenerators (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) : C :=
  ∐ (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X)

/-- 第一ブロックの置換と全単射で添字付けた、関係式の余積。 -/
def freeBlockRelations (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) : C :=
  ∐ (fun _ : Equiv.Perm (Fin (m - n)) × FreeBlockIndex n m =>
    F.obj (FiniteBijection.of (m - n)) ⊗ X)

/-- 関係式の左辺は第一ブロックの作用をテンソル積へ作用させる。 -/
def freeBlockRelationLeft (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockRelations F n X m ⟶ freeBlockGenerators F n X m :=
  Sigma.desc (fun r => F.map (FiniteBijection.permutation (m - n) r.1) ▷ X ≫
    Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) r.2)

/-- 関係式の右辺は第一ブロックの置換を全単射の添字へ前合成する。 -/
def freeBlockRelationRight (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockRelations F n X m ⟶ freeBlockGenerators F n X m :=
  Sigma.desc (fun r =>
    Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X)
      (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) r.1) (𝟙 _) ≫ r.2))

/-- 第一ブロックの対称群の関係式で割った明示的な余等化子。 -/
def freeBlockQuotient (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) : C :=
  coequalizer (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m)

/-- 全単射の添字に対応する商の生成元。 -/
def freeBlockQuotientGenerator (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (h : FreeBlockIndex n m) : F.obj (FiniteBijection.of (m - n)) ⊗ X ⟶
      freeBlockQuotient F n X m :=
  Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫
    coequalizer.π (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m)

/-- 商の生成元は第一ブロックの対称群の関係式を満たす。 -/
@[reassoc] lemma freeBlockQuotientGenerator_relation (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) (σ : Equiv.Perm (Fin (m - n))) (h : FreeBlockIndex n m) :
    F.map (FiniteBijection.permutation (m - n) σ) ▷ X ≫
        freeBlockQuotientGenerator F n X m h =
      freeBlockQuotientGenerator F n X m
        (FiniteBijection.sumMap (FiniteBijection.permutation (m - n) σ) (𝟙 _) ≫ h) := by
  have hc := congrArg (fun t =>
    Sigma.ι (fun _ : Equiv.Perm (Fin (m - n)) × FreeBlockIndex n m =>
      F.obj (FiniteBijection.of (m - n)) ⊗ X) (σ, h) ≫ t)
    (coequalizer.condition (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m))
  simpa only [freeBlockQuotientGenerator, freeBlockRelationLeft, freeBlockRelationRight,
    Sigma.ι_comp_desc_assoc, Category.assoc] using hc

/-- 固定次数の生成元の余積から、自由convolutionの各段への射。 -/
def freeBlockProjection (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockGenerators F n X m ⟶ level (convolution F ((freeAt n).obj X)) m :=
  Sigma.desc (fun h => freeConvolutionGenerator F n X m (FiniteBijection.of (m - n)) h)

/-- 商からの射は全ての生成元上の値で決まる。 -/
lemma freeBlockQuotient_hom_ext (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    {Y : C} (f g : freeBlockQuotient F n X m ⟶ Y)
    (h : ∀ k, freeBlockQuotientGenerator F n X m k ≫ f =
      freeBlockQuotientGenerator F n X m k ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro k
  simpa only [freeBlockQuotientGenerator, Category.assoc] using h k

/-- 各段への射は第一ブロックの作用の関係式を同一視する。 -/
lemma freeBlockProjection_condition (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockRelationLeft F n X m ≫ freeBlockProjection F n X m =
      freeBlockRelationRight F n X m ≫ freeBlockProjection F n X m := by
  apply Sigma.hom_ext
  intro r
  simp only [freeBlockRelationLeft, freeBlockRelationRight, freeBlockProjection,
    Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc]
  exact freeConvolutionGenerator_left_relation F n X m
    (FiniteBijection.permutation (m - n) r.1) r.2

/-- 自由convolutionの各段を頂点とする、ブロックの関係式の余錐。 -/
def freeBlockCofork (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    Cofork (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m) :=
  Cofork.ofπ (freeBlockProjection F n X m) (freeBlockProjection_condition F n X m)

variable [MonoidalClosed C]

/-- 商の余錐から、全ての第一ブロックの生成元上の射の族を復元する。 -/
def freeBlockCoforkFamily (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ)
    (c : Cofork (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m)) :
    FreeConvolutionFamily F n X m c.pt where
  app a h := by
    have ha : a = FiniteBijection.of (m - n) := by
      have hc : FiniteBijection.card a = m - n :=
        freeInduction_card n m (CostructuredArrow.mk (Y := a) h)
      exact (FiniteBijection.of_card a).symm.trans (congrArg FiniteBijection.of hc)
    subst a
    exact Sigma.ι (fun _ : FreeBlockIndex n m =>
      F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫ c.π
  relation {a b} k h := by
    have hb : b = FiniteBijection.of (m - n) := by
      have hc : FiniteBijection.card b = m - n :=
        freeInduction_card n m (CostructuredArrow.mk (Y := b) h)
      exact (FiniteBijection.of_card b).symm.trans (congrArg FiniteBijection.of hc)
    have ha : a = b := FiniteBijection.object_eq_of_hom k
    subst a
    subst b
    change F.map k ▷ X ≫
        (Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫
          c.π) =
      Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X)
        (FiniteBijection.sumMap k (𝟙 _) ≫ h) ≫ c.π
    have hc := congrArg (fun t =>
      Sigma.ι (fun _ : Equiv.Perm (Fin (m - n)) × FreeBlockIndex n m =>
        F.obj (FiniteBijection.of (m - n)) ⊗ X) (FiniteBijection.equivOfHom k, h) ≫ t)
      c.condition
    simpa only [freeBlockRelationLeft, freeBlockRelationRight, Sigma.ι_comp_desc_assoc,
      FiniteBijection.permutation, FiniteBijection.homOfEquiv_equivOfHom, Category.assoc] using hc

/-- 自由convolutionの各段は、明示的なブロック商の普遍性を持つ。 -/
def freeBlockCoforkIsColimit (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    IsColimit (freeBlockCofork F n X m) :=
  Cofork.IsColimit.mk _ (fun c => (freeBlockCoforkFamily F n X m c).desc)
    (fun c => by
      apply Sigma.hom_ext
      intro h
      change Sigma.ι _ h ≫ freeBlockProjection F n X m ≫
        (freeBlockCoforkFamily F n X m c).desc = Sigma.ι _ h ≫ c.π
      rw [freeBlockProjection, Sigma.ι_comp_desc_assoc, FreeConvolutionFamily.desc_fac]
      rfl)
    (fun c f hf => by
      apply freeConvolutionLevel_hom_ext_standard
      intro h
      have hh := congrArg (fun t =>
        Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫ t) hf
      change Sigma.ι _ h ≫ freeBlockProjection F n X m ≫ f = Sigma.ι _ h ≫ c.π at hh
      rw [freeBlockProjection, Sigma.ι_comp_desc_assoc] at hh
      rw [FreeConvolutionFamily.desc_fac]
      exact hh)

/-- 自由convolutionの各段は、第一ブロックの対称群の関係式による余等化子。 -/
def freeConvolutionLevelIsoBlockQuotient (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    level (convolution F ((freeAt n).obj X)) m ≅ freeBlockQuotient F n X m :=
  (freeBlockCoforkIsColimit F n X m).coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (freeBlockRelationLeft F n X m)
      (freeBlockRelationRight F n X m)))

/-- 比較同型は固定次数の生成元を商の標準包含へ送る。 -/
@[reassoc] lemma freeConvolutionLevelIsoBlockQuotient_generator
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (h : FreeBlockIndex n m) :
    freeConvolutionGenerator F n X m (FiniteBijection.of (m - n)) h ≫
        (freeConvolutionLevelIsoBlockQuotient F n X m).hom =
      Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫
        coequalizer.π (freeBlockRelationLeft F n X m) (freeBlockRelationRight F n X m) := by
  have hc := (freeBlockCoforkIsColimit F n X m).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (parallelPair (freeBlockRelationLeft F n X m)
      (freeBlockRelationRight F n X m)))
      WalkingParallelPair.one
  have hh := congrArg (fun t =>
    Sigma.ι (fun _ : FreeBlockIndex n m => F.obj (FiniteBijection.of (m - n)) ⊗ X) h ≫ t) hc
  change Sigma.ι _ h ≫ freeBlockProjection F n X m ≫ _ = _ at hh
  rw [freeBlockProjection, Sigma.ι_comp_desc_assoc] at hh
  exact hh

/-- 比較同型の逆は商の生成元を自由convolutionの生成元へ戻す。 -/
@[reassoc] lemma freeConvolutionLevelIsoBlockQuotient_inverse
    (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ (freeConvolutionLevelIsoBlockQuotient F n X m).inv =
      freeConvolutionGenerator F n X m (FiniteBijection.of (m - n)) h := by
  rw [freeBlockQuotientGenerator, ← freeConvolutionLevelIsoBlockQuotient_generator,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 明示的なブロック商と、第二ブロックnの誘導図式の余極限との比較。 -/
def freeBlockQuotientIsoInduction (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) :
    freeBlockQuotient F n X m ≅ colimit (freeInductionDiagram F n X m) :=
  (freeConvolutionLevelIsoBlockQuotient F n X m).symm ≪≫
    freeConvolutionLevelIsoInduction F n X m

/-- 誘導図式への比較は商の生成元を標準包含へ送る。 -/
@[reassoc] lemma freeBlockQuotientIsoInduction_generator (F : SymmetricSequence C)
    (n : ℕ) (X : C) (m : ℕ) (h : FreeBlockIndex n m) :
    freeBlockQuotientGenerator F n X m h ≫ (freeBlockQuotientIsoInduction F n X m).hom =
      colimit.ι (freeInductionDiagram F n X m)
        (CostructuredArrow.mk (Y := FiniteBijection.of (m - n)) h) := by
  change freeBlockQuotientGenerator F n X m h ≫
    (freeConvolutionLevelIsoBlockQuotient F n X m).inv ≫
      (freeConvolutionLevelIsoInduction F n X m).hom = _
  rw [freeConvolutionLevelIsoBlockQuotient_inverse_assoc]
  exact freeConvolutionLevelIsoInduction_generator F n X m
    (CostructuredArrow.mk (Y := FiniteBijection.of (m - n)) h)

end SerrePositivity.SymmetricSequence
