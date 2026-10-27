module
public import SerrePositivity.KST.Spectra.S3ActualFaces
public import SerrePositivity.KST.Spectra.S3MilnorConnection
public import SerrePositivity.KST.Spectra.S3KappaConnection

/-!
概要：Sp-3 専用の s3 消費側集約。
方針：三認証の明示代入口、元始域屋根、K-B3 の既存 strict 屋根への接続を公開する。
規約：K-S• ③ の実認証の存在と s3 の無条件化は未供給。共有集約は変更しない。
使われ方：独立ビルドと scripts/audit_kst_spectra_s3.lean。
-/
