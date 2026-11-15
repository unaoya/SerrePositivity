module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasArrowFamily
public import SerrePositivity.AlgebraicGeometry.BaseChangedOverlapTriple

/-!
概要：有限族として同じ段に降ろした射を、実際の段の gluing datum の三種の射へ移す。
方針：対角・反転を有限和から読み、三重交叉は具体的な底変換同型で移送する。
規約：逆・cocycle の式は後の共通段へ降ろす別の法則で与える。
使われ方：G2 の有限表示対象の模型の gluing datum の組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] [IsNoetherianRing k]
  {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)
  {B : Scheme.{u}} (γ : B ⟶ Spec (CommRingCat.of m.A))
  (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)

/-- 有限族から読み出した、段の対角の逆の候補。 -/
def stageDiagonal (i : I) :
    pullback γ (m.map i) ⟶ pullback γ ((m.overlap i i).ι ≫ m.map i) :=
  l (.inl i)

/-- 有限族から読み出した、段の重なりの反転。 -/
def stageReverse (i a : I) :
    pullback γ ((m.overlap i a).ι ≫ m.map i) ⟶
      pullback γ ((m.overlap a i).ι ≫ m.map a) :=
  l (.inr (.inl (i, a)))

/-- 段の実際の三重交叉へ同型で移した、次の重なりへの射。 -/
def stageTriple (i a b : I) :
    pullback (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
      (baseChangedOverlapMap γ (m.map i) (m.overlap i b).ι) ⟶
      pullback γ ((m.overlap a b).ι ≫ m.map a) :=
  (baseChangedOverlapTripleIso γ (m.map i) (m.overlap i a).ι (m.overlap i b).ι).hom ≫
    l (.inr (.inr (i, a, b)))

variable (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
  pullback.fst γ (m.atlasArrowFamily e).sourceMap)
include hl

/-- 段の対角の逆の候補は同じ基底上の射。 -/
theorem stageDiagonal_toBase (i : I) :
    m.stageDiagonal γ l i ≫ pullback.fst γ ((m.overlap i i).ι ≫ m.map i) =
      pullback.fst γ (m.map i) := hl (.inl i)

/-- 段の反転は同じ基底上の射。 -/
theorem stageReverse_toBase (i a : I) :
    m.stageReverse γ l i a ≫ pullback.fst γ ((m.overlap a i).ι ≫ m.map a) =
      pullback.fst γ ((m.overlap i a).ι ≫ m.map i) := hl (.inr (.inl (i, a)))

/-- 三重交叉の移送後にも同じ基底上の射。 -/
theorem stageTriple_toBase (i a b : I) :
    m.stageTriple γ l i a b ≫ pullback.fst γ ((m.overlap a b).ι ≫ m.map a) =
      pullback.fst (baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι)
        (baseChangedOverlapMap γ (m.map i) (m.overlap i b).ι) ≫
      baseChangedOverlapMap γ (m.map i) (m.overlap i a).ι ≫ pullback.fst γ (m.map i) := by
  dsimp only [stageTriple]
  have he : l (.inr (.inr (i, a, b))) ≫
      pullback.fst γ ((m.overlap a b).ι ≫ m.map a) =
      pullback.fst γ (pullback.fst (m.overlap i a).ι (m.overlap i b).ι ≫
        (m.overlap i a).ι ≫ m.map i) := hl (.inr (.inr (i, a, b)))
  rw [Category.assoc, he]
  exact baseChangedOverlapTripleIso_hom_fst γ (m.map i) (m.overlap i a).ι (m.overlap i b).ι

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
