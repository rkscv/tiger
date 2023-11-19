#![feature(assert_matches)]
#![feature(get_mut_unchecked)]
#![feature(iterator_try_collect)]
#![feature(test)]

#[macro_use]
extern crate pest_derive;
extern crate test;

pub mod ast;
pub mod env;
pub mod error;
pub mod parser;
pub mod vm;

#[cfg(test)]
mod tests {
    use crate::{
        ast::WithSpan,
        error::{Error, ErrorVariant},
        parser, vm,
    };
    use std::{assert_matches::assert_matches, io};
    use std::{fs, path::PathBuf};
    use test::Bencher;

    fn test(file_name: &str, src: &str) -> Result<(), Error> {
        let ast = parser::parse(src)?;
        if !["merge.tig", "test6.tig", "test7.tig", "test18.tig"].contains(&file_name) {
            vm::eval(&ast)?;
        }
        Ok(())
    }

    fn test_sample(file_name: &str) -> Result<(), Error> {
        let src = fs::read_to_string(["testcases", file_name].iter().collect::<PathBuf>()).unwrap();
        test(file_name, &src)
    }

    #[rustfmt::skip]
    #[test]
    fn test_samples() {
        assert_matches!(test_sample("merge.tig"), Ok(_));
        assert_matches!(test_sample("queens.tig"), Ok(_));
        assert_matches!(test_sample("test1.tig"), Ok(_));
        assert_matches!(test_sample("test2.tig"), Ok(_));
        assert_matches!(test_sample("test3.tig"), Ok(_));
        assert_matches!(test_sample("test4.tig"), Ok(_));
        assert_matches!(test_sample("test5.tig"), Ok(_));
        assert_matches!(test_sample("test6.tig"), Ok(_));
        assert_matches!(test_sample("test7.tig"), Ok(_));
        assert_matches!(test_sample("test8.tig"), Ok(_));
        assert_matches!(test_sample("test9.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test10.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test11.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test12.tig"), Ok(_));
        assert_matches!(test_sample("test13.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnsupportedOperandTypes { .. }, .. })));
        assert_matches!(test_sample("test14.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnsupportedOperandTypes { .. }, .. })));
        assert_matches!(test_sample("test15.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test16.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::RecursiveType(_), .. })));
        assert_matches!(test_sample("test17.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotDefined(_), .. })));
        assert_matches!(test_sample("test18.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotDefined(_), .. })));
        assert_matches!(test_sample("test19.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotDefined(_), .. })));
        assert_matches!(test_sample("test20.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotDefined(_), .. })));
        assert_matches!(test_sample("test21.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnsupportedOperandTypes { .. }, .. })));
        assert_matches!(test_sample("test22.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NoSuchField(_), .. })));
        assert_matches!(test_sample("test23.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test24.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotArray(_), .. })));
        assert_matches!(test_sample("test25.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotRecord(_), .. })));
        assert_matches!(test_sample("test26.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnsupportedOperandTypes { .. }, .. })));
        assert_matches!(test_sample("test27.tig"), Ok(_));
        assert_matches!(test_sample("test28.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test29.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test30.tig"), Ok(_));
        assert_matches!(test_sample("test31.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test32.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test33.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::NotDefined(_), .. })));
        assert_matches!(test_sample("test34.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test35.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedArgumentNum { .. }, .. })));
        assert_matches!(test_sample("test36.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedArgumentNum { .. }, .. })));
        assert_matches!(test_sample("test37.tig"), Ok(_));
        assert_matches!(test_sample("test38.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::DuplicateDefinitions(_), .. })));
        assert_matches!(test_sample("test39.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::DuplicateDefinitions(_), .. })));
        assert_matches!(test_sample("test40.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::MismatchedTypes { .. }, .. })));
        assert_matches!(test_sample("test41.tig"), Ok(_));
        assert_matches!(test_sample("test42.tig"), Ok(_));
        assert_matches!(test_sample("test43.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnsupportedOperandTypes { .. }, .. })));
        assert_matches!(test_sample("test44.tig"), Ok(_));
        assert_matches!(test_sample("test45.tig"), Err(Error::Variant(WithSpan { inner: ErrorVariant::UnknownType(_), .. })));
        assert_matches!(test_sample("test46.tig"), Ok(_));
        assert_matches!(test_sample("test47.tig"), Ok(_));
        assert_matches!(test_sample("test48.tig"), Ok(_));
        assert_matches!(test_sample("test49.tig"), Err(Error::ParseError(_)));
    }

    #[bench]
    fn bench_samples(b: &mut Bencher) -> io::Result<()> {
        let samples = fs::read_dir("testcases")?
            .map(|sample| -> io::Result<_> {
                let sample = sample?;
                Ok((
                    sample.file_name().into_string().unwrap(),
                    fs::read_to_string(sample.path())?,
                ))
            })
            .try_collect::<Vec<_>>()?;
        b.iter(|| {
            for (file_name, src) in &samples {
                _ = test(file_name, src);
            }
        });
        Ok(())
    }

    #[bench]
    fn bench_samples_front_end(b: &mut Bencher) -> io::Result<()> {
        let samples = fs::read_dir("testcases")?
            .map(|sample| fs::read_to_string(sample?.path()))
            .try_collect::<Vec<_>>()?;
        b.iter(|| {
            for src in &samples {
                _ = parser::parse(src);
            }
        });
        Ok(())
    }
}
