module
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorTriangulated
public import SerrePositivity.InfinityCategories.Stable.HomotopyNatTransPrecomposition
public import SerrePositivity.InfinityCategories.Stable.ShiftCommutationNaturalTransformation

/-! # 完全関手間の単体的自然変換

概要：完全関手間の単体的ホモトピーが誘導する自然変換を cofiber 接続射と照合する。
方針：cofiber 四角形に前合成し、四角形の比較の接続射の自然性を適用する。
規約：自然変換の成分の可逆性は仮定しない。使われ方：S6 のシフトと両立する自然変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：完全関手間の単体的自然変換が誘導する h の自然変換。
方針：指定両端を持つホモトピーの各頂点の縦辺を取る。
規約：成分の可逆性は不要。使われ方：完全関手の間の二胞体。 -/
def exactFunctorNatTrans {X Y : SSet.{u}} {F G : X ⟶ Y}
    [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G) :
    (hoFunctor.map F).toFunctor ⟶ (hoFunctor.map G).toFunctor :=
  homotopyNatTransOfEndpoints H.h H.h₀ H.h₁

/-- 概要：完全関手間の単体的自然変換は像の cofiber 接続射と可換。
方針：四角形に前合成したホモトピーに接続射の自然性を適用し、成分を元の自然変換へ戻す。
規約：安定な quasicategory 間の完全関手で、任意の成分を許す。
使われ方：懸垂との交換の自然性。 -/
lemma exactFunctorNatTrans_cofiberConnecting {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G)
    (t : ZeroTriangle X) (ht : IsCofiberSequence t) :
    (exactFunctorNatTrans H).app t.hoShortComplex.X₃ ≫
        cofiberConnecting (t.map G (IsExactFunctor.preservesZero (F := G)))
          (IsExactFunctor.preservesCofiber (F := G) t ht) =
      cofiberConnecting (t.map F (IsExactFunctor.preservesZero (F := F)))
          (IsExactFunctor.preservesCofiber (F := F) t ht) ≫
        (suspensionFunctor Y).map ((exactFunctorNatTrans H).app t.hoShortComplex.X₁) := by
  let d := t.map F (IsExactFunctor.preservesZero (F := F))
  let e := t.map G (IsExactFunctor.preservesZero (F := G))
  let Q := stableHomotopyPrecomp t.square H
  let m := d.hoShortComplexMapOfHomotopy e Q.h Q.h₀ Q.h₁
  have hc₁ : m.τ₁ = (exactFunctorNatTrans H).app t.hoShortComplex.X₁ := by
    apply Arrow.mk_injective
    exact homotopyNatTransOfEndpoints_precomp_app_arrow t.square H
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0)
  have hc₃ : m.τ₃ = (exactFunctorNatTrans H).app t.hoShortComplex.X₃ := by
    apply Arrow.mk_injective
    exact homotopyNatTransOfEndpoints_precomp_app_arrow t.square H
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1)
  have hn := cofiberConnecting_naturality_of_homotopy d e
    (IsExactFunctor.preservesCofiber (F := F) t ht)
    (IsExactFunctor.preservesCofiber (F := G) t ht) Q
  change m.τ₃ ≫ cofiberConnecting e _ =
    cofiberConnecting d _ ≫ (suspensionFunctor Y).map m.τ₁ at hn
  rw [hc₁, hc₃] at hn
  exact hn

/-- 概要：cofiber 列の中間頂点が零なら懸垂に値を持つ接続射は同型。
方針：distinguished triangle の中間対象の零性から第三射の可逆性を得て、懸垂との比較を戻す。
規約：安定な quasicategory。使われ方：懸垂の自然変換の照合で接続射を消去する。 -/
lemma cofiberConnecting_isIso_of_zero_middle {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (t : ZeroTriangle X) (ht : IsCofiberSequence t)
    (hz : IsZeroVertex (squareVertex t.square 1 0)) : IsIso (cofiberConnecting t ht) := by
  have hT : cofiberTriangle t ht ∈ distTriang (hoFunctor.obj X) :=
    cofiberTriangle_mem_cofiberDistinguishedTriangles t ht
  have : IsIso (cofiberTriangle t ht).mor₃ :=
    ((cofiberTriangle t ht).isZero₂_iff_isIso₃ hT).1 hz.isZeroHo
  have he : cofiberConnecting t ht = (cofiberTriangle t ht).mor₃ ≫
      (shiftOneSuspensionIso X).hom.app t.hoShortComplex.X₁ := by
    change cofiberConnecting t ht =
      (cofiberConnecting t ht ≫ (shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁) ≫
        (shiftOneSuspensionIso X).hom.app t.hoShortComplex.X₁
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [he]
  infer_instance

/-- 概要：零の中間対象を持つ列の始点では、単体的自然変換は懸垂比較と可換。
方針：像の接続射の自然性を完全関手の接続射保存で書き直し、可逆な接続射を消去する。
規約：自然変換の成分自体の可逆性は不要。使われ方：任意の始点の懸垂との交換。 -/
lemma exactFunctorNatTrans_suspension_comm_of_zero_middle {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G)
    (t : ZeroTriangle X) (ht : IsCofiberSequence t)
    (hz : IsZeroVertex (squareVertex t.square 1 0)) :
    (exactFunctorNatTrans H).app ((suspensionFunctor X).obj t.hoShortComplex.X₁) ≫
        (exactFunctorSuspensionIso G).hom.app t.hoShortComplex.X₁ =
      (exactFunctorSuspensionIso F).hom.app t.hoShortComplex.X₁ ≫
        (suspensionFunctor Y).map ((exactFunctorNatTrans H).app t.hoShortComplex.X₁) := by
  have := cofiberConnecting_isIso_of_zero_middle t ht hz
  apply (cancel_epi ((hoFunctor.map F).toFunctor.map (cofiberConnecting t ht))).1
  have hn := exactFunctorNatTrans_cofiberConnecting H t ht
  rw [← cofiberConnecting_postcomp G t ht, ← cofiberConnecting_postcomp F t ht] at hn
  have hnat := (exactFunctorNatTrans H).naturality (cofiberConnecting t ht)
  have hh := (congrArg (fun a ↦ a ≫
      (exactFunctorSuspensionIso G).hom.app t.hoShortComplex.X₁) hnat).trans
    ((Category.assoc _ _ _).trans hn)
  simpa only [Category.assoc] using hh

/-- 概要：完全関手間の単体的自然変換は懸垂との標準比較と可換。
方針：任意の始点の suspension 四角形に零中間対象の消去を適用する。
規約：全ての対象で、可逆性を仮定しない自然変換。使われ方：一回シフトとの両立。 -/
lemma exactFunctorNatTrans_suspension_comm {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G)
    (x : X _⦋0⦌) :
    (exactFunctorNatTrans H).app ((suspensionFunctor X).obj (SSet.HomotopyCategory.mk x)) ≫
        (exactFunctorSuspensionIso G).hom.app (SSet.HomotopyCategory.mk x) =
      (exactFunctorSuspensionIso F).hom.app (SSet.HomotopyCategory.mk x) ≫
        (suspensionFunctor Y).map ((exactFunctorNatTrans H).app (SSet.HomotopyCategory.mk x)) := by
  let s := chosenSuspensionSquare x
  have h := exactFunctorNatTrans_suspension_comm_of_zero_middle H
    s.toZeroTriangle s.isPushout s.other_zero
  change (exactFunctorNatTrans H).app
      ((suspensionFunctor X).obj (SSet.HomotopyCategory.mk (squareVertex s.square 0 0))) ≫
      (exactFunctorSuspensionIso G).hom.app
        (SSet.HomotopyCategory.mk (squareVertex s.square 0 0)) =
    (exactFunctorSuspensionIso F).hom.app
        (SSet.HomotopyCategory.mk (squareVertex s.square 0 0)) ≫
      (suspensionFunctor Y).map ((exactFunctorNatTrans H).app
        (SSet.HomotopyCategory.mk (squareVertex s.square 0 0))) at h
  have hx : squareVertex s.square 0 0 = x := s.source_eq
  rw [hx] at h
  exact h

/-- 概要：完全関手間の単体的自然変換は一回シフトとの比較と可換。
方針：懸垂との可換式をシフトと懸垂の自然同型で輸送する。
規約：Mathlib の CommShiftCore の一回シフトの条件。使われ方：全整数への延長。 -/
lemma exactFunctorNatTrans_commShift_one {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G) :
    NatTrans.CommShiftCore (exactFunctorNatTrans H) (1 : ℤ) := by
  constructor
  apply NatTrans.ext
  funext x
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
  change X _⦋0⦌ at x
  change ((hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ)).hom.app
      (SSet.HomotopyCategory.mk x) ≫
      (shiftFunctor (hoFunctor.obj Y) (1 : ℤ)).map
        ((exactFunctorNatTrans H).app (SSet.HomotopyCategory.mk x)) =
    (exactFunctorNatTrans H).app
        ((shiftFunctor (hoFunctor.obj X) (1 : ℤ)).obj (SSet.HomotopyCategory.mk x)) ≫
      ((hoFunctor.map G).toFunctor.commShiftIso (1 : ℤ)).hom.app (SSet.HomotopyCategory.mk x)
  rw [exactFunctorCommShift_one, exactFunctorCommShift_one]
  simp only [exactFunctorShiftOneIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← (shiftOneSuspensionIso Y).inv.naturality
    ((exactFunctorNatTrans H).app (SSet.HomotopyCategory.mk x))]
  rw [← reassoc_of% exactFunctorNatTrans_suspension_comm H x]
  rw [reassoc_of% (exactFunctorNatTrans H).naturality
    ((shiftOneSuspensionIso X).hom.app (SSet.HomotopyCategory.mk x))]

/-- 概要：完全関手間の単体的自然変換は全整数シフトと両立する。
方針：一回シフトとの可換性を整合的な整数延長へ移す。
規約：Mathlib の NatTrans.CommShift instance。使われ方：h の三角関手間の自然変換。 -/
instance exactFunctorNatTrans_commShift {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G) :
    NatTrans.CommShift (exactFunctorNatTrans H) ℤ := by
  apply stableNatTransCommShiftOfOne (exactFunctorNatTrans H)
    (exactFunctorShiftOneIso F) (exactFunctorShiftOneIso G)
  intro x
  have hx := NatTrans.congr_app (exactFunctorNatTrans_commShift_one H).shift_comm x
  change ((hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ)).hom.app x ≫
      (shiftFunctor (hoFunctor.obj Y) (1 : ℤ)).map ((exactFunctorNatTrans H).app x) =
    (exactFunctorNatTrans H).app ((shiftFunctor (hoFunctor.obj X) (1 : ℤ)).obj x) ≫
      ((hoFunctor.map G).toFunctor.commShiftIso (1 : ℤ)).hom.app x at hx
  rw [exactFunctorCommShift_one, exactFunctorCommShift_one] at hx
  exact hx

/-- 概要：完全関手間の単体的自然変換は三角形の像の間の自然変換を誘導する。
方針：三つの成分は元の自然変換で取り、第三の可換式にはシフトとの両立を使う。
規約：任意の三角形で自然。使われ方：S6 の三角関手間の自然変換の具体的な公開。 -/
def exactFunctorNatTransTriangle {X Y : SSet.{u}}
    [Quasicategory X] [IsStable X] [Quasicategory Y] [IsStable Y]
    {F G : X ⟶ Y} [IsExactFunctor F] [IsExactFunctor G] (H : SSet.Homotopy F G) :
    (hoFunctor.map F).toFunctor.mapTriangle ⟶ (hoFunctor.map G).toFunctor.mapTriangle where
  app T := {
    hom₁ := (exactFunctorNatTrans H).app T.obj₁
    hom₂ := (exactFunctorNatTrans H).app T.obj₂
    hom₃ := (exactFunctorNatTrans H).app T.obj₃
    comm₁ := (exactFunctorNatTrans H).naturality T.mor₁
    comm₂ := (exactFunctorNatTrans H).naturality T.mor₂
    comm₃ := by
      change ((hoFunctor.map F).toFunctor.map T.mor₃ ≫
          ((hoFunctor.map F).toFunctor.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          (shiftFunctor (hoFunctor.obj Y) (1 : ℤ)).map ((exactFunctorNatTrans H).app T.obj₁) =
        (exactFunctorNatTrans H).app T.obj₃ ≫
          ((hoFunctor.map G).toFunctor.map T.mor₃ ≫
            ((hoFunctor.map G).toFunctor.commShiftIso (1 : ℤ)).hom.app T.obj₁)
      rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc,
        (exactFunctorNatTrans H).naturality, Category.assoc] }
  naturality {T U} f := by
    apply Pretriangulated.Triangle.hom_ext
    · exact (exactFunctorNatTrans H).naturality f.hom₁
    · exact (exactFunctorNatTrans H).naturality f.hom₂
    · exact (exactFunctorNatTrans H).naturality f.hom₃

end SerrePositivity.InfinityCategories
