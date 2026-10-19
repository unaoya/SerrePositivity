module

public import SerrePositivity.KST.Spectra.SkeletonFiltrationMono
public import SerrePositivity.KST.Spectra.CartesianSubfunctorColimit

/-!
概要：単体集合の図式の各単体次数で、有限骨格を Type 値の部分図式として表示する。
方針：骨格の射影の値は元の図式の射そのものであり、単射なら所属を反映することを使う。
規約：図式の全ての射が単射である場合に余極限での単射性へ接続する。
使われ方：Goerss–Jardine VIII §1。骨格の latching 図式の各単体次数。
-/

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits SSet
namespace SerrePositivity.KST.Spectra.SkeletonDiagramSubfunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {J : Type v} [SmallCategory J] (D : J ⥤ SSet.{u}) (n : ℕ)
  (k : SimplexCategoryᵒᵖ)

/-- 有限骨格の各次数での部分図式。 -/
def subfunctor : Subfunctor (D ⋙ (evaluation _ (Type u)).obj k) where
  obj j := ((D.obj j).skeleton n).obj k
  map f := (Subcomplex.image_le_iff _ (D.map f) _).1 (SkeletonFiltration.image_le (D.map f) n) k

/-- 部分図式としての表示と実際の骨格の評価は同じ。 -/
def iso : (D ⋙ SkeletonFiltration.functor n) ⋙ (evaluation _ (Type u)).obj k ≅
    (subfunctor D n k).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext x; rfl)

/-- 上の同型は実際の骨格の包含を保つ。 -/
lemma iso_inclusion : (iso D n k).hom ≫ (subfunctor D n k).ι =
    Functor.whiskerRight (Functor.whiskerLeft D (SkeletonFiltration.inclusion n))
      ((evaluation _ (Type u)).obj k) := by
  apply NatTrans.ext
  funext j
  rfl

/-- 図式の射が単射なら、各次数の部分図式の所属を保存・反映する。 -/
lemma membership_iff (hD : ∀ {i j : J} (f : i ⟶ j), Mono (D.map f))
    {i j : J} (f : i ⟶ j) (x : (D.obj i).obj k) :
    (D.map f).app k x ∈ (subfunctor D n k).obj j ↔ x ∈ (subfunctor D n k).obj i := by
  let : Mono (D.map f) := hD f
  change x ∈ (((D.obj j).skeleton n).preimage (D.map f)).obj k ↔
    x ∈ ((D.obj i).skeleton n).obj k
  rw [SkeletonFiltration.preimage_skeleton]

/-- 全ての図式の射が単射なら、各次数での骨格の余極限の包含も単射。 -/
lemma colimit_mono [HasColimitsOfShape J (Type u)]
    (hD : ∀ {i j : J} (f : i ⟶ j), Mono (D.map f)) :
    Mono (colim.map (Functor.whiskerRight
      (Functor.whiskerLeft D (SkeletonFiltration.inclusion n))
      ((evaluation _ (Type u)).obj k))) := by
  rw [← iso_inclusion D n k, Functor.map_comp]
  let : Mono (colim.map (subfunctor D n k).ι) :=
    CartesianSubfunctorColimit.mono (subfunctor D n k) (membership_iff D n k hD)
  infer_instance

end SerrePositivity.KST.Spectra.SkeletonDiagramSubfunctor
