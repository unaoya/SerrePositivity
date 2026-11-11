module

public import SerrePositivity.KST.Spectra.TrianglePairRoundTrip
public import SerrePositivity.KST.Spectra.ReducedSquarePullback
public import SerrePositivity.KST.Spectra.SquareSmashExt

/-!
概要：二つの円の smash 積は二つの相対三角形の貼り合わせである。
方針：正方形の境界を潰す構成と、制限・貼り合わせの厳密な計算を使う。
規約：共通の対角辺は同じ円からの二つの包含である。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二重 loop の変数交換の幾何的比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：二つの単体的な円の smash 積。
方針：通常の点つき smash を使う。
規約：正方形の四辺を潰した対象を表す。
使われ方：Goerss–Jardine I §7。相対三角形の貼り合わせの余頂点。 -/
abbrev circleSmashSquare : PointedSimplicialSet.{u} :=
  PointedObject.smash PointedSimplicialSet.circle.{u} PointedSimplicialSet.circle.{u}

/-- 概要：正方形から二つの円の smash 積への標準射。
方針：二つの円への商射の積に smash の商射を合成する。
規約：座標の順序は保つ。
使われ方：Kerodon §3.2.3（Tag 00W3）。三角形の制限と写像の等式判定。 -/
abbrev circleSmashSquareQuotient :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ circleSmashSquare.{u}.right :=
  (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
    PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
      (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
        PointedSimplicialSet.circle.{u}).right

/-- 概要：標準の正方形の商射は縦辺を潰す。
方針：smash の商の reduced 条件を引き戻す。
規約：恒等射の reduced 表示を使う。
使われ方：Goerss–Jardine I §7。上側・下側の制限の存在条件。 -/
theorem circleSmashSquareQuotient_left :
    (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫ circleSmashSquareQuotient =
      toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ circleSmashSquare.{u}.hom := by
  simpa only [PointedObject.smashToReduced, Under.id_right, Category.comp_id,
    Category.assoc] using reducedSquare_boundary_left
      (PointedObject.smashToReduced (𝟙 circleSmashSquare.{u}))

/-- 概要：標準の正方形の商射は横辺を潰す。
方針：第二変数の reduced 条件を正方形へ引き戻す。
規約：smash の標準の基点を使う。
使われ方：Goerss–Jardine I §7。相対三角形への制限の存在条件。 -/
theorem circleSmashSquareQuotient_right :
    (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫ circleSmashSquareQuotient =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ circleSmashSquare.{u}.hom := by
  simpa only [PointedObject.smashToReduced, Under.id_right, Category.comp_id,
    Category.assoc] using reducedSquare_boundary_right
      (PointedObject.smashToReduced (𝟙 circleSmashSquare.{u}))

/-- 概要：上側の相対三角形から二つの円の smash 積への包含。
方針：正方形の商射を上側へ制限する。
規約：ホーン Λ[2,1] の商からの点つき射。
使われ方：Kerodon §3.2.3（Tag 00W3）。三角形による pushout の第一の脚。 -/
def circleSmashUpper : triangleDisk.{u} ⟶ circleSmashSquare.{u} :=
  squareUpperRestriction _ circleSmashSquareQuotient
    circleSmashSquareQuotient_left circleSmashSquareQuotient_right

/-- 概要：下側の相対三角形から二つの円の smash 積への包含。
方針：正方形の商射を下側へ制限する。
規約：上側と同じ相対三角形を源とする。
使われ方：Kerodon §3.2.3（Tag 00W3）。三角形による pushout の第二の脚。 -/
def circleSmashLower : triangleDisk.{u} ⟶ circleSmashSquare.{u} :=
  squareLowerRestriction _ circleSmashSquareQuotient
    circleSmashSquareQuotient_left circleSmashSquareQuotient_right

/-- 概要：二つの包含は共通の対角辺で一致する。
方針：正方形の制限の対角辺での一致を使う。
規約：対角辺の向きは両方で同じ。
使われ方：Goerss–Jardine I §7。三角形の貼り合わせの可換条件。 -/
theorem circleSmashTriangles_comm :
    triangleDiskDiagonal ≫ circleSmashUpper.{u} =
      triangleDiskDiagonal ≫ circleSmashLower.{u} :=
  squareRestrictions_diagonal _ _ _ _

/-- 概要：上側の包含は標準三角形上で正方形の商射に一致する。
方針：制限の商射での式を使う。
規約：基礎単体集合の射の等式。
使われ方：Goerss–Jardine I §7。pushout の第一の脚の計算。 -/
@[reassoc (attr := simp)]
theorem circleSmashUpper_quotient :
    triangleDiskQuotient ≫ circleSmashUpper.{u}.right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ circleSmashSquareQuotient :=
  squareUpperRestriction_quotient _ _ _ _

/-- 概要：下側の包含は標準三角形上で正方形の商射に一致する。
方針：制限の商射での式を使う。
規約：上側と同じ商射を使う。
使われ方：Goerss–Jardine I §7。pushout の第二の脚の計算。 -/
@[reassoc (attr := simp)]
theorem circleSmashLower_quotient :
    triangleDiskQuotient ≫ circleSmashLower.{u}.right =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ circleSmashSquareQuotient :=
  squareLowerRestriction_quotient _ _ _ _

/-- 概要：相対三角形の貼り合わせは上側で第一の写像へ戻る。
方針：相対三角形の商射上で正方形の復元の式を使う。
規約：共通の対角辺での一致を仮定する。
使われ方：Kerodon §3.2.3（Tag 00W3）。pushout の降下の第一の式。 -/
@[reassoc (attr := simp)]
theorem circleSmashUpper_pair {Y : PointedSimplicialSet.{u}}
    (a b : triangleDisk.{u} ⟶ Y) (h : triangleDiskDiagonal ≫ a = triangleDiskDiagonal ≫ b) :
    circleSmashUpper ≫ trianglePairSmash a b h = a := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp only [Under.comp_right, circleSmashUpper_quotient_assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫
    ((PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right ≫ (trianglePairSmash a b h).right) = _
  erw [trianglePairSmash_quotient, upper_trianglePairSquare]

/-- 概要：相対三角形の貼り合わせは下側で第二の写像へ戻る。
方針：相対三角形の商射上で正方形の復元の式を使う。
規約：上側と同じ貼り合わせを使う。
使われ方：Kerodon §3.2.3（Tag 00W3）。pushout の降下の第二の式。 -/
@[reassoc (attr := simp)]
theorem circleSmashLower_pair {Y : PointedSimplicialSet.{u}}
    (a b : triangleDisk.{u} ⟶ Y) (h : triangleDiskDiagonal ≫ a = triangleDiskDiagonal ≫ b) :
    circleSmashLower ≫ trianglePairSmash a b h = b := by
  apply PointedObject.cofiber_hom_ext (horn.{u} 2 (1 : Fin 3)).ι
  simp only [Under.comp_right, circleSmashLower_quotient_assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫
    ((PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right ≫ (trianglePairSmash a b h).right) = _
  erw [trianglePairSmash_quotient, lower_trianglePairSquare]

/-- 概要：二つの相対三角形上での一致は smash 積からの射の一致を与える。
方針：正方形上で判定してから二つの三角形の pushout で判定する。
規約：比較する射は任意の点つき標的へ向かう。
使われ方：Goerss–Jardine I §7。三角形の pushout の一意性。 -/
theorem circleSmashTriangles_hom_ext {Y : PointedSimplicialSet.{u}}
    {f g : circleSmashSquare.{u} ⟶ Y}
    (hu : circleSmashUpper ≫ f = circleSmashUpper ≫ g)
    (hl : circleSmashLower ≫ f = circleSmashLower ≫ g) : f = g := by
  apply squareSmash_hom_ext
  change circleSmashSquareQuotient ≫ f.right = circleSmashSquareQuotient ≫ g.right
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.isPushout.hom_ext
  · have h := congrArg (fun k : triangleDisk.{u} ⟶ Y => triangleDiskQuotient ≫ k.right) hu
    simpa only [Under.comp_right, circleSmashUpper_quotient_assoc,
      Category.assoc] using h
  · have h := congrArg (fun k : triangleDisk.{u} ⟶ Y => triangleDiskQuotient ≫ k.right) hl
    simpa only [Under.comp_right, circleSmashLower_quotient_assoc,
      Category.assoc] using h

/-- 概要：二つの円の smash 積は二つの相対三角形を対角辺で貼った pushout。
方針：四辺の商で構成した降下と、正方形で判定する一意性を合わせる。
規約：点つき単体集合の圏での厳密な pushout。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。写像空間を二つの相対三角形の pullback として表す。 -/
theorem circleSmashTriangles_isPushout :
    IsPushout triangleDiskDiagonal triangleDiskDiagonal circleSmashUpper.{u} circleSmashLower := by
  apply IsPushout.mk' circleSmashTriangles_comm
  · intro Y f g hu hl
    exact circleSmashTriangles_hom_ext hu hl
  · intro Y a b h
    exact ⟨trianglePairSmash a b h, circleSmashUpper_pair a b h, circleSmashLower_pair a b h⟩

end

end SerrePositivity.KST.Spectra
