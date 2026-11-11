module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
概要：Čech 版の Rees 比較に使う、短複体の任意直和とコホモロジーの交換。
方針：ModuleCat の AB4 と ShortComplex.mapHomologyIso を使い、各成分の包含を保つ。
規約：添字は Type、加群は基底環と同じ宇宙に置く。
使われ方：Stacks 30.20.1 の Hⁱ に対応する射影 Čech 版の有限性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {κ : Type} [DecidableEq κ]

/-- 加群の外部直和を余錐にする。 -/
abbrev projectiveDirectSumCofan (M : κ → ModuleCat.{u} R) : Cofan M :=
  Cofan.mk (ModuleCat.of R (⨁ n, M n))
    (fun n ↦ ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ M n) n))

/-- 外部直和の余錐の普遍性。 -/
def projectiveDirectSumCofanIsColimit (M : κ → ModuleCat.{u} R) :
    IsColimit (projectiveDirectSumCofan M) where
  desc s := ModuleCat.ofHom (DirectSum.toModule R κ s.pt
    (fun n ↦ (s.ι.app ⟨n⟩).hom))
  fac s n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact @DirectSum.toModule_lof R inferInstance κ (fun n ↦ (M n : Type u))
      (fun n ↦ inferInstance) (fun n ↦ inferInstance) inferInstance
      (s.pt : Type u) inferInstance inferInstance (fun n ↦ (s.ι.app ⟨n⟩).hom) n.as x
  uniq s f hf := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change f.hom (DirectSum.lof R κ (fun n ↦ M n) n x) =
      DirectSum.toModule R κ s.pt (fun n ↦ (s.ι.app ⟨n⟩).hom)
        (DirectSum.lof R κ (fun n ↦ M n) n x)
    calc
      _ = (s.ι.app ⟨n⟩).hom x := congrArg (fun g ↦ g.hom x) (hf ⟨n⟩)
      _ = _ := (@DirectSum.toModule_lof R inferInstance κ (fun n ↦ (M n : Type u))
        (fun n ↦ inferInstance) (fun n ↦ inferInstance) inferInstance
        (s.pt : Type u) inferInstance inferInstance (fun n ↦ (s.ι.app ⟨n⟩).hom) n x).symm

/-- カテゴリーの余極限を外部直和と比較する。 -/
def projectiveDirectSumColimitIso (M : κ → ModuleCat.{u} R) :
    colimit (Discrete.functor M) ≅ ModuleCat.of R (⨁ n, M n) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (projectiveDirectSumCofanIsColimit M)

/-- 余極限の比較は各成分の包含を保つ。 -/
@[reassoc (attr := simp)]
theorem projectiveDirectSumColimitIso_ι (M : κ → ModuleCat.{u} R) (n : κ) :
    colimit.ι (Discrete.functor M) ⟨n⟩ ≫ (projectiveDirectSumColimitIso M).hom =
      ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ M n) n) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

/-- 成分ごとの写像の余極限は、比較の下で直和写像となる。 -/
theorem projectiveDirectSumColimitIso_naturality
    {M N : κ → ModuleCat.{u} R} (f : ∀ n, M n ⟶ N n) :
    colim.map (Discrete.natTrans (F := Discrete.functor M) (G := Discrete.functor N) (fun n ↦ f n.as)) ≫
        (projectiveDirectSumColimitIso N).hom =
      (projectiveDirectSumColimitIso M).hom ≫
        ModuleCat.ofHom (DirectSum.lmap (fun n ↦ (f n).hom)) := by
  apply colimit.hom_ext
  intro n
  rcases n with ⟨n⟩
  rw [colimit.ι_map_assoc]
  change f n ≫ colimit.ι (Discrete.functor N) ⟨n⟩ ≫
      (projectiveDirectSumColimitIso N).hom =
    colimit.ι (Discrete.functor M) ⟨n⟩ ≫ (projectiveDirectSumColimitIso M).hom ≫
      ModuleCat.ofHom (DirectSum.lmap (fun n ↦ (f n).hom))
  rw [projectiveDirectSumColimitIso_ι, projectiveDirectSumColimitIso_ι_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (DirectSum.lmap_lof (fun n ↦ (f n).hom) n x).symm

variable (S : κ → ShortComplex (ModuleCat.{u} R))

/-- 短複体の族を、離散図式の短複体としてまとめる。 -/
def projectiveShortComplexDiagram : ShortComplex (Discrete κ ⥤ ModuleCat.{u} R) where
  X₁ := Discrete.functor (fun n ↦ (S n).X₁)
  X₂ := Discrete.functor (fun n ↦ (S n).X₂)
  X₃ := Discrete.functor (fun n ↦ (S n).X₃)
  f := Discrete.natTrans (fun n ↦ (S n.as).f)
  g := Discrete.natTrans (fun n ↦ (S n.as).g)
  zero := by
    apply NatTrans.ext
    funext n
    exact (S n.as).zero

/-- 各項の直和を取った短複体。 -/
def projectiveDirectSumShortComplex : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (DirectSum.lmap (fun n ↦ (S n).f.hom)))
    (ModuleCat.ofHom (DirectSum.lmap (fun n ↦ (S n).g.hom))) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro n
      change (S n).g.hom ((S n).f.hom (x n)) = 0
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (S n).zero) (x n))

/-- 短複体の余極限を、各項の外部直和と比較する。 -/
def projectiveDirectSumShortComplexIso :
    (projectiveShortComplexDiagram S).map (colim (J := Discrete κ)) ≅
      projectiveDirectSumShortComplex S :=
  ShortComplex.isoMk (projectiveDirectSumColimitIso (fun n ↦ (S n).X₁))
    (projectiveDirectSumColimitIso (fun n ↦ (S n).X₂))
    (projectiveDirectSumColimitIso (fun n ↦ (S n).X₃))
    (projectiveDirectSumColimitIso_naturality (fun n ↦ (S n).f)).symm
    (projectiveDirectSumColimitIso_naturality (fun n ↦ (S n).g)).symm

/-- 離散図式のコホモロジーの各成分を、元の短複体のコホモロジーと比較する。 -/
def projectiveShortComplexDiagramHomologyIso :
    (projectiveShortComplexDiagram S).homology ≅
      Discrete.functor (fun n ↦ (S n).homology) :=
  Discrete.natIso (fun n ↦
    ((projectiveShortComplexDiagram S).mapHomologyIso
      ((evaluation (Discrete κ) (ModuleCat.{u} R)).obj n)).symm)

/-- 短複体の任意直和のコホモロジーは、各コホモロジーの直和。
Čech 版の Rees 有限性（原典 Stacks 30.20.1 の Hⁱ）への代数的な比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveDirectSumShortComplexHomologyIso :
    (projectiveDirectSumShortComplex S).homology ≅
      ModuleCat.of R (⨁ n, (S n).homology) :=
  ((ShortComplex.homologyFunctor (ModuleCat.{u} R)).mapIso
    (projectiveDirectSumShortComplexIso S)).symm ≪≫
    (projectiveShortComplexDiagram S).mapHomologyIso (colim (J := Discrete κ)) ≪≫
    (colim (J := Discrete κ)).mapIso (projectiveShortComplexDiagramHomologyIso S) ≪≫
    projectiveDirectSumColimitIso (fun n ↦ (S n).homology)

end SerrePositivity.AlgebraicGeometry
