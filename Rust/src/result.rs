#[derive(Debug)]
pub enum Error {
    Init(String),
    Goal(String),
    Guide(String),
    Rewrite(String),
    Failed,
}

impl ToString for Error {

    fn to_string(&self) -> String {
        match self {
            Error::Init(s)    => format!("⚡️ {s}"),
            Error::Goal(s)    => format!("⚡️ {s}"),
            Error::Guide(s)   => format!("⚡️ {s}"),
            Error::Rewrite(s) => format!("⚡️ {s}"),
            Error::Failed     => "".to_string(),
        }
    }
}

pub type Res<T> = Result<T, Error>;