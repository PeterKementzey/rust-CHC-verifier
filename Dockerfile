FROM rust:alpine
RUN apk update && apk add z3 && apk add python3
WORKDIR /usr/src/myapp
COPY . .
CMD python3 -u verify.py
